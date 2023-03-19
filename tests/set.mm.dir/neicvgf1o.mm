include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "ccom.mm"
include "wf1o.mm"
include "cvv.mm"
include "wcel.mm"
include "neicvgbex.mm"
include "pwexg.mm"
include "syl.mm"
include "fsovf1od.mm"
include "dssmapf1od.mm"
include "f1oco.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wb.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem neicvgf1o
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
  assert |- ( ph -> H : ( ~P ~P B ^m B ) -1-1-onto-> ( ~P ~P B ^m B ) )

  proof
    wph
    cB
    cpw
    #
    cpw
    cB
    cmap
    co
    #
    @1
    cF
    cD
    cG
    ccom
    #
    ccom
    #
    wf1o
    #
    @1
    @1
    cH
    wf1o
    #
    wph
    @0
    @0
    cmap
    co
    #
    @1
    cF
    wf1o
    @1
    @6
    @2
    wf1o
    #
    @4
    wph
    vm
    vl
    @0
    cB
    vk
    cF
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    wph
    cB
    cvv
    wcel
    @0
    cvv
    wcel
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
    #
    cB
    cvv
    pwexg
    syl
    #
    @8
    neicvg.f
    fsovf1od
    wph
    @6
    @6
    cD
    wf1o
    @1
    @6
    cG
    wf1o
    @7
    wph
    cB
    cD
    vp
    cP
    cvv
    vo
    vn
    neicvg.p
    neicvg.d
    @8
    dssmapf1od
    wph
    vm
    vl
    cB
    @0
    vk
    cG
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    @8
    @9
    neicvg.g
    fsovf1od
    @1
    @6
    @6
    cD
    cG
    f1oco
    syl2anc
    @1
    @6
    @1
    cF
    @2
    f1oco
    syl2anc
    cH
    @3
    wceq
    @5
    @4
    wb
    neicvg.h
    @1
    @1
    cH
    @3
    f1oeq1
    ax-mp
    sylibr
end
