include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "ccom.mm"
include "wf1o.mm"
include "cvv.mm"
include "wcel.mm"
include "clsneibex.mm"
include "wa.mm"
include "pwexg.mm"
include "adantl.mm"
include "simpr.mm"
include "eqid.mm"
include "fsovf1od.mm"
include "dssmapf1od.mm"
include "f1oco.mm"
include "syl2anc.mm"
include "mpdan.mm"
include "wceq.mm"
include "wb.mm"
include "coeq12i.mm"
include "eqtri.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem clsneif1o
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
  assert |- ( ph -> H : ( ~P B ^m ~P B ) -1-1-onto-> ( ~P ~P B ^m B ) )

  proof
    wph
    cB
    cpw
    #
    @0
    cmap
    co
    #
    @0
    cpw
    cB
    cmap
    co
    #
    @0
    cB
    cO
    co
    #
    cB
    cP
    cfv
    #
    ccom
    #
    wf1o
    #
    @1
    @2
    cH
    wf1o
    #
    wph
    cB
    cvv
    wcel
    #
    @6
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
    @2
    @3
    wf1o
    @1
    @1
    @4
    wf1o
    @6
    @9
    vm
    vl
    @0
    cB
    vk
    @3
    cO
    cvv
    cvv
    vi
    vj
    clsnei.o
    @8
    @0
    cvv
    wcel
    wph
    cB
    cvv
    pwexg
    adantl
    wph
    @8
    simpr
    #
    @3
    eqid
    fsovf1od
    @9
    cB
    @4
    vp
    cP
    cvv
    vo
    vn
    clsnei.p
    @4
    eqid
    @10
    dssmapf1od
    @1
    @1
    @2
    @3
    @4
    f1oco
    syl2anc
    mpdan
    cH
    @5
    wceq
    @7
    @6
    wb
    cH
    cF
    cD
    ccom
    @5
    clsnei.h
    cF
    @3
    cD
    @4
    clsnei.f
    clsnei.d
    coeq12i
    eqtri
    @1
    @2
    cH
    @5
    f1oeq1
    ax-mp
    sylibr
end
