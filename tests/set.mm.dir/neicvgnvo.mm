include "ccnv.mm"
include "ccom.mm"
include "cnveqi.mm"
include "cnvco.mm"
include "coeq1i.mm"
include "3eqtri.mm"
include "cpw.mm"
include "cvv.mm"
include "neicvgbex.mm"
include "wcel.mm"
include "pwexg.mm"
include "syl.mm"
include "fsovcnvd.mm"
include "dssmapnvod.mm"
include "coeq12d.mm"
include "syl5eq.mm"
include "coass.mm"
include "eqtr4i.mm"
include "syl6eq.mm"

theorem neicvgnvo
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
  assert |- ( ph -> `' H = H )

  proof
    wph
    cH
    ccnv
    #
    cF
    cD
    ccom
    #
    cG
    ccom
    #
    cH
    wph
    @0
    cG
    ccnv
    #
    cD
    ccnv
    #
    ccom
    #
    cF
    ccnv
    #
    ccom
    #
    @2
    @0
    cF
    cD
    cG
    ccom
    #
    ccom
    #
    ccnv
    @8
    ccnv
    #
    @6
    ccom
    @7
    cH
    @9
    neicvg.h
    cnveqi
    cF
    @8
    cnvco
    @10
    @5
    @6
    cD
    cG
    cnvco
    coeq1i
    3eqtri
    wph
    @5
    @1
    @6
    cG
    wph
    @3
    cF
    @4
    cD
    wph
    vm
    vl
    cB
    cB
    cpw
    #
    vk
    cG
    cF
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
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
    wph
    cB
    cvv
    wcel
    @11
    cvv
    wcel
    @12
    cB
    cvv
    pwexg
    syl
    #
    neicvg.g
    neicvg.f
    fsovcnvd
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
    @12
    dssmapnvod
    coeq12d
    wph
    vm
    vl
    @11
    cB
    vk
    cF
    cG
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    @13
    @12
    neicvg.f
    neicvg.g
    fsovcnvd
    coeq12d
    syl5eq
    @2
    @9
    cH
    cF
    cD
    cG
    coass
    neicvg.h
    eqtr4i
    syl6eq
end
