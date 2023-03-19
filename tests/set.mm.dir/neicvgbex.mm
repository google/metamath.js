include "cfv.mm"
include "ccom.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "coeq1i.mm"
include "coeq2i.mm"
include "eqtri.mm"
include "a1i.mm"
include "breqdi.mm"
include "brne0.mm"
include "wn.mm"
include "cdm.mm"
include "crn.mm"
include "cin.mm"
include "fvprc.mm"
include "dmeqd.mm"
include "dm0.mm"
include "syl6eq.mm"
include "ineq1d.mm"
include "incom.mm"
include "in0.mm"
include "coemptyd.mm"
include "rneqd.mm"
include "rn0.mm"
include "ineq2d.mm"
include "necon1ai.mm"
include "3syl.mm"

theorem neicvgbex
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  assume neicvgbex.d: |- D = ( P ` B )
  assume neicvgbex.h: |- H = ( F o. ( D o. G ) )
  assume neicvgbex.r: |- ( ph -> N H M )


  assert |- ( ph -> B e. _V )

  proof
    wph
    cN
    cM
    cF
    cB
    cP
    cfv
    #
    cG
    ccom
    #
    ccom
    #
    wbr
    @2
    c0
    wne
    cB
    cvv
    wcel
    #
    wph
    cH
    @2
    cN
    cM
    cH
    @2
    wceq
    wph
    cH
    cF
    cD
    cG
    ccom
    #
    ccom
    @2
    neicvgbex.h
    @4
    @1
    cF
    cD
    @0
    cG
    neicvgbex.d
    coeq1i
    coeq2i
    eqtri
    a1i
    neicvgbex.r
    breqdi
    cN
    cM
    @2
    brne0
    @3
    @2
    c0
    @3
    wn
    #
    cF
    @1
    @5
    cF
    cdm
    #
    @1
    crn
    #
    cin
    @6
    c0
    cin
    c0
    @5
    @7
    c0
    @6
    @5
    @7
    c0
    crn
    c0
    @5
    @1
    c0
    @5
    @0
    cG
    @5
    @0
    cdm
    #
    cG
    crn
    #
    cin
    c0
    @9
    cin
    #
    c0
    @5
    @8
    c0
    @9
    @5
    @8
    c0
    cdm
    c0
    @5
    @0
    c0
    cB
    cP
    fvprc
    dmeqd
    dm0
    syl6eq
    ineq1d
    @10
    @9
    c0
    cin
    c0
    c0
    @9
    incom
    @9
    in0
    eqtri
    syl6eq
    coemptyd
    rneqd
    rn0
    syl6eq
    ineq2d
    @6
    in0
    syl6eq
    coemptyd
    necon1ai
    3syl
end
