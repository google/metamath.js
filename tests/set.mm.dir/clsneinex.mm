include "cfv.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "clsneibex.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "wfn.mm"
include "pwexg.mm"
include "adantl.mm"
include "simpr.mm"
include "fsovf1od.mm"
include "f1ofn.mm"
include "syl.mm"
include "wf.mm"
include "dssmapf1od.mm"
include "f1of.mm"
include "ccom.mm"
include "adantr.mm"
include "breqi.mm"
include "sylib.mm"
include "brcoffn.mm"
include "mpdan.mm"
include "simprd.mm"
include "ntrneinex.mm"

theorem clsneinex
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
  assert |- ( ph -> N e. ( ~P ~P B ^m B ) )

  proof
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cK
    cD
    cfv
    #
    cN
    cO
    vl
    clsnei.o
    clsnei.f
    wph
    cK
    @0
    cD
    wbr
    #
    @0
    cN
    cF
    wbr
    #
    wph
    cB
    cvv
    wcel
    #
    @1
    @2
    wa
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
    @3
    wa
    #
    cK
    cN
    cF
    cD
    cB
    cpw
    #
    @5
    cmap
    co
    #
    @6
    @4
    @6
    @5
    cpw
    cB
    cmap
    co
    #
    cF
    wf1o
    cF
    @6
    wfn
    @4
    vm
    vl
    @5
    cB
    vk
    cF
    cO
    cvv
    cvv
    vi
    vj
    clsnei.o
    @3
    @5
    cvv
    wcel
    wph
    cB
    cvv
    pwexg
    adantl
    wph
    @3
    simpr
    #
    clsnei.f
    fsovf1od
    @6
    @7
    cF
    f1ofn
    syl
    @4
    @6
    @6
    cD
    wf1o
    @6
    @6
    cD
    wf
    @4
    cB
    cD
    vp
    cP
    cvv
    vo
    vn
    clsnei.p
    clsnei.d
    @8
    dssmapf1od
    @6
    @6
    cD
    f1of
    syl
    @4
    cK
    cN
    cH
    wbr
    #
    cK
    cN
    cF
    cD
    ccom
    #
    wbr
    wph
    @9
    @3
    clsnei.r
    adantr
    cK
    cN
    cH
    @10
    clsnei.h
    breqi
    sylib
    brcoffn
    mpdan
    simprd
    ntrneinex
end
