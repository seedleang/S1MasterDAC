# -*- coding: utf-8 -*-
import numpy as np
import pickle as pkl
import matplotlib.pyplot as plt



def learnHMM(allx, allq, N, K, initTo1=False):
    """
    Apprend les paramètres d'un modèle HMM par comptage d'une série de séquences étiquetée
    :param allx: observations
    [[obs1, ... , obsT], [obs1, ..., obsT], ...]
         Seq 1                 Seq 2        ...
    :param allq: étiquetage
    [[s1, ... , sT], [s1, ..., sT], ...]
         Seq 1            Seq 2        ...
    :param N: nombre d'états
    :param K: nombre d'observations
    :param initTo1: initialisation à 1 (ou epsilon) pour éviter les proba 0
    :return: Pi, A, B
    Les matrices de paramétrage des HMM
    """
    if initTo1:
        eps = 1e-8
        #A = 1-np.tri(N)*eps
        A = np.ones((N,N))*eps
        B = np.ones((N,K))*eps
        #Pi = np.zeros(N)
        Pi = np.ones(N)*eps
    else:
        A = np.zeros((N,N))
        B = np.zeros((N,K))
        Pi = np.zeros(N)
    for x,q in zip(allx,allq):
        Pi[int(q[0])] += 1
        for i in range(len(q)-1):
            A[int(q[i]),int(q[i+1])] += 1
            B[int(q[i]),int(x[i])] += 1
        B[int(q[-1]),int(x[-1])] += 1 # derniere transition
    A = A/np.maximum(A.sum(1).reshape(N,1),1) # normalisation
    B = B/np.maximum(B.sum(1).reshape(N,1),1) # normalisation
    Pi = Pi/Pi.sum()
    return Pi , A, B

# pour B discret
def calc_log_pobs(x, Pi,A,B):
    """
    Algorithme alpha de calcul de la vraisemblance d'une séquence d'observations sachant le modèle
    p(x | lambda)
    :param x: [obs1, ... , obsT] (UNE séquence)
    :param Pi: param HMM
    :param A: param HMM
    :param B: param HMM
    :return: log(p(x | lambda))
    """
    T = len(x)
    N = len(Pi)
    alpha = np.zeros((N,T))
    omega = np.zeros(T)
    alpha[:,0] = Pi * B[:,x[0]]
    omega[0] = alpha[:,0].sum()
    alpha[:,0] /= omega[0]
    for t in range(1,T):
        alpha[:,t] = alpha[:,t-1].reshape(1,N).dot(A) * B[:,x[t]]
        omega[t] = alpha[:,t].sum()
        alpha[:,t] /= omega[t]
    return np.log(omega).sum() #, omega


def viterbi(x,Pi,A,B):
    """
    Algorithme de Viterbi (en log) pour le décodage des séquences d'états:
    argmax_s p(x, s | lambda)
    :param x: [obs1, ... , obsT] (UNE séquence)
    :param Pi: param HMM
    :param A: param HMM
    :param B: param HMM
    :return: s (la séquence d'état la plus probable), estimation de p(x|lambda)
    """
    T = len(x)
    N = len(Pi)
    logA = np.log(A)
    logB = np.log(B)
    logdelta = np.zeros((N,T))
    psi = np.zeros((N,T), int)
    S = np.zeros(T, int)
    logdelta[:,0] = np.log(Pi) + logB[:,x[0]]
    #forward
    for t in range(1,T):
        logdelta[:,t] = (logdelta[:,t-1].reshape(N,1) + logA).max(0) + logB[:,x[t]]
        psi[:,t] = (logdelta[:,t-1].reshape(N,1) + logA).argmax(0)
    # backward
    logp = logdelta[:,-1].max()
    S[T-1] = logdelta[:,-1].argmax()
    for i in range(2,T+1):
        S[int(T-i)] = psi[S[T-i+1],int(T-i+1)]
    return S, logp


def viterbi_contraintes(x,Pi,A,B, states):
    """
    Algorithme de Viterbi (en log) pour le décodage des séquences d'états:
    argmax_s p(x, s | lambda)
    :param x: [obs1, ... , obsT] (UNE séquence)
    :param Pi: param HMM
    :param A: param HMM
    :param B: param HMM
    :return: s (la séquence d'état la plus probable), estimation de p(x|lambda)
    """
    T = len(x)
    N = len(Pi)
    logA = np.log(A)
    logB = np.log(B)
    logdelta = np.zeros((N,T))
    psi = np.zeros((N,T), int)
    S = np.zeros(T, int)
    logdelta[:,0] = np.log(Pi) + logB[:,x[0]]
    #forward
    for t in range(1,T):
        logdelta[:,t] = (logdelta[:,t-1].reshape(N,1) + logA).max(0) + logB[:,x[t]]
        psi[:, t] = (logdelta[:, t - 1].reshape(N, 1) + logA).argmax(0)
        if states[t] != -1:
            logdelta[[i for i in range(N) if i != states[t]], t] = -1e8
    # backward
    logp = logdelta[:,-1].max()
    S[T-1] = logdelta[:,-1].argmax()
    for i in range(2,T+1):
        S[T-i] = psi[S[T-i+1],int(T-i+1)]
    return S, logp

