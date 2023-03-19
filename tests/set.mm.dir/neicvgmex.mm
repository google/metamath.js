include "cfv.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "neicvgbex.mm"
include "wa.mm"
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
include "fsovfd.mm"
include "ccom.mm"
include "breqi.mm"
include "sylib.mm"
include "adantr.mm"
include "brcofffn.mm"
include "mpdan.mm"
include "simp3d.mm"
include "ntrneinex.mm"

theorem neicvgmex
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
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cO: class O
  let vp: setvar p
  let vl: setvar l
  assume neicvg.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume neicvg.p: |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |-> ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) )
  assume neicvg.d: |- D = ( P ` B )
  assume neicvg.f: |- F = ( ~P B O B )
  assume neicvg.g: |- G = ( B O ~P B )
  assume neicvg.h: |- H = ( F o. ( D o. G ) )
  assume neicvg.r: |- ( ph -> N H M )

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
  assert |- ( ph -> M e. ( ~P ~P B ^m B ) )

  proof
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cN
    cG
    cfv
    #
    cD
    cfv
    #
    cM
    cO
    vl
    neicvg.o
    neicvg.f
    wph
    cN
    @0
    cG
    wbr
    #
    @0
    @1
    cD
    wbr
    #
    @1
    cM
    cF
    wbr
    #
    wph
    cB
    cvv
    wcel
    #
    @2
    @3
    @4
    w3a
    wph
    cB
    cD
    cP
    cF
    cG
    cH
    cM
    cN
    neicvg.d
    neicvg.h
    neicvg.r
    neicvgbex
    wph
    @5
    wa
    #
    cN
    cM
    cF
    cD
    cG
    cB
    cpw
    #
    cpw
    cB
    cmap
    co
    #
    @7
    @7
    cmap
    co
    #
    @9
    @6
    @9
    @8
    cF
    wf1o
    cF
    @9
    wfn
    @6
    vm
    vl
    @7
    cB
    vk
    cF
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    @5
    @7
    cvv
    wcel
    wph
    cB
    cvv
    pwexg
    adantl
    #
    wph
    @5
    simpr
    #
    neicvg.f
    fsovf1od
    @9
    @8
    cF
    f1ofn
    syl
    @6
    @9
    @9
    cD
    wf1o
    @9
    @9
    cD
    wf
    @6
    cB
    cD
    vp
    cP
    cvv
    vo
    vn
    neicvg.p
    neicvg.d
    @11
    dssmapf1od
    @9
    @9
    cD
    f1of
    syl
    @6
    vm
    vl
    cB
    @7
    vk
    cG
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    @11
    @10
    neicvg.g
    fsovfd
    wph
    cN
    cM
    cF
    cD
    cG
    ccom
    ccom
    #
    wbr
    #
    @5
    wph
    cN
    cM
    cH
    wbr
    @13
    neicvg.r
    cN
    cM
    cH
    @12
    neicvg.h
    breqi
    sylib
    adantr
    brcofffn
    mpdan
    simp3d
    ntrneinex
end
