include "cdm.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "dmexg.mm"
include "syl.mm"
include "cpr.mm"
include "wss.mm"
include "cop.mm"
include "wceq.mm"
include "dmpropg.mm"
include "syl2anc.mm"
include "dmss.mm"
include "eqsstr3d.mm"
include "wa.mm"
include "wb.mm"
include "prssg.mm"
include "wi.mm"
include "neeq1.mm"
include "neeq2.mm"
include "rspc2ev.mm"
include "3expa.mm"
include "expcom.mm"
include "sylbird.mm"
include "mpd.mm"
include "hashge2el2difr.mm"

theorem hashdmpropge2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume hashdmpropge2.a: |- ( ph -> A e. V )
  assume hashdmpropge2.b: |- ( ph -> B e. W )
  assume hashdmpropge2.c: |- ( ph -> C e. X )
  assume hashdmpropge2.d: |- ( ph -> D e. Y )
  assume hashdmpropge2.f: |- ( ph -> F e. Z )
  assume hashdmpropge2.n: |- ( ph -> A =/= B )
  assume hashdmpropge2.s: |- ( ph -> { <. A , C >. , <. B , D >. } C_ F )


  assert |- ( ph -> 2 <_ ( # ` dom F ) )

  proof
    wph
    cF
    cdm
    #
    cvv
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    vb
    @0
    wrex
    va
    @0
    wrex
    #
    c2
    @0
    chash
    cfv
    cle
    wbr
    wph
    cF
    cZ
    wcel
    @1
    hashdmpropge2.f
    cF
    cZ
    dmexg
    syl
    wph
    cA
    cB
    cpr
    #
    @0
    wss
    #
    @5
    wph
    @6
    cA
    cC
    cop
    cB
    cD
    cop
    cpr
    #
    cdm
    #
    @0
    wph
    cC
    cX
    wcel
    cD
    cY
    wcel
    @9
    @6
    wceq
    hashdmpropge2.c
    hashdmpropge2.d
    cA
    cC
    cB
    cD
    cX
    cY
    dmpropg
    syl2anc
    wph
    @8
    cF
    wss
    @9
    @0
    wss
    hashdmpropge2.s
    @8
    cF
    dmss
    syl
    eqsstr3d
    wph
    @7
    cA
    @0
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    @5
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    @12
    @7
    wb
    hashdmpropge2.a
    hashdmpropge2.b
    cA
    cB
    @0
    cV
    cW
    prssg
    syl2anc
    wph
    cA
    cB
    wne
    #
    @12
    @5
    wi
    hashdmpropge2.n
    @12
    @13
    @5
    @10
    @11
    @13
    @5
    @4
    @13
    cA
    @3
    wne
    va
    vb
    cA
    cB
    @0
    @0
    @2
    cA
    @3
    neeq1
    @3
    cB
    cA
    neeq2
    rspc2ev
    3expa
    expcom
    syl
    sylbird
    mpd
    va
    vb
    @0
    cvv
    hashge2el2difr
    syl2anc
end
