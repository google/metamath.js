include "cfv.mm"
include "ccom.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
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
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "ineq2d.mm"
include "in0.mm"
include "coemptyd.mm"
include "necon1ai.mm"
include "3syl.mm"

theorem clsneibex
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cF: class F
  let cH: class H
  let cK: class K
  let cN: class N
  assume clsneibex.d: |- D = ( P ` B )
  assume clsneibex.h: |- H = ( F o. D )
  assume clsneibex.r: |- ( ph -> K H N )


  assert |- ( ph -> B e. _V )

  proof
    wph
    cK
    cN
    cF
    cB
    cP
    cfv
    #
    ccom
    #
    wbr
    @1
    c0
    wne
    cB
    cvv
    wcel
    #
    wph
    cH
    @1
    cK
    cN
    cH
    @1
    wceq
    wph
    cH
    cF
    cD
    ccom
    @1
    clsneibex.h
    cD
    @0
    cF
    clsneibex.d
    coeq2i
    eqtri
    a1i
    clsneibex.r
    breqdi
    cK
    cN
    @1
    brne0
    @2
    @1
    c0
    @2
    wn
    #
    cF
    @0
    @3
    cF
    cdm
    #
    @0
    crn
    #
    cin
    @4
    c0
    cin
    c0
    @3
    @5
    c0
    @4
    @3
    @5
    c0
    crn
    c0
    @3
    @0
    c0
    cB
    cP
    fvprc
    rneqd
    rn0
    syl6eq
    ineq2d
    @4
    in0
    syl6eq
    coemptyd
    necon1ai
    3syl
end
