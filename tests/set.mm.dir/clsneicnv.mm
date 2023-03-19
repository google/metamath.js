include "ccnv.mm"
include "ccom.mm"
include "cpw.mm"
include "co.mm"
include "cnveqi.mm"
include "cnvco.mm"
include "eqtri.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "clsneibex.mm"
include "wa.mm"
include "simpr.mm"
include "dssmapnvod.mm"
include "pwexg.mm"
include "adantl.mm"
include "eqid.mm"
include "fsovcnvd.mm"
include "coeq12d.mm"
include "mpdan.mm"
include "syl5eq.mm"

theorem clsneicnv
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let cF: class F
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let vp: setvar p
  let vl: setvar l
  assume clsnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume clsnei.p: |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |-> ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) )
  assume clsnei.d: |- D = ( P ` B )
  assume clsnei.f: |- F = ( ~P B O B )
  assume clsnei.h: |- H = ( F o. D )
  assume clsnei.r: |- ( ph -> K H N )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint B n
  disjoint B o
  disjoint B p
  disjoint n o
  disjoint n p
  disjoint o p
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint n ph
  disjoint o ph
  disjoint p ph
  assert |- ( ph -> `' H = ( D o. ( B O ~P B ) ) )

  proof
    wph
    cH
    ccnv
    #
    cD
    ccnv
    #
    cF
    ccnv
    #
    ccom
    #
    cD
    cB
    cB
    cpw
    #
    cO
    co
    #
    ccom
    #
    @0
    cF
    cD
    ccom
    #
    ccnv
    @3
    cH
    @7
    clsnei.h
    cnveqi
    cF
    cD
    cnvco
    eqtri
    wph
    cB
    cvv
    wcel
    #
    @3
    @6
    wceq
    wph
    cB
    cD
    cP
    cF
    cH
    cK
    cN
    clsnei.d
    clsnei.h
    clsnei.r
    clsneibex
    wph
    @8
    wa
    #
    @1
    cD
    @2
    @5
    @9
    cB
    cD
    vp
    cP
    cvv
    vo
    vn
    clsnei.p
    clsnei.d
    wph
    @8
    simpr
    #
    dssmapnvod
    @9
    vm
    vl
    @4
    cB
    vk
    cF
    @5
    cO
    cvv
    cvv
    vi
    vj
    clsnei.o
    @8
    @4
    cvv
    wcel
    wph
    cB
    cvv
    pwexg
    adantl
    @10
    clsnei.f
    @5
    eqid
    fsovcnvd
    coeq12d
    mpdan
    syl5eq
end
