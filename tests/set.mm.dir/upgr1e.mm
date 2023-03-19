include "cupgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf.mm"
include "cpr.mm"
include "cop.mm"
include "prex.mm"
include "snid.mm"
include "a1i.mm"
include "fsnd.mm"
include "wss.mm"
include "prssd.mm"
include "syl6sseq.mm"
include "elpw.mm"
include "sylibr.mm"
include "upgr1elem.mm"
include "fssd.mm"
include "cvv.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbird.mm"
include "dmeqd.mm"
include "feq12d.mm"
include "wb.mm"
include "1vgrex.mm"
include "eqid.mm"
include "isupgr.mm"
include "3syl.mm"

theorem upgr1e
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume upgr1e.v: |- V = ( Vtx ` G )
  assume upgr1e.a: |- ( ph -> A e. X )
  assume upgr1e.b: |- ( ph -> B e. V )
  assume upgr1e.c: |- ( ph -> C e. V )
  assume upgr1e.e: |- ( ph -> ( iEdg ` G ) = { <. A , { B , C } >. } )


  assert |- ( ph -> G e. UPGraph )

  proof
    wph
    cG
    cupgr
    wcel
    #
    cG
    ciedg
    cfv
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    #
    vx
    cG
    cvtx
    cfv
    #
    cpw
    #
    c0
    csn
    #
    cdif
    crab
    #
    @1
    wf
    #
    wph
    @8
    cA
    cB
    cC
    cpr
    #
    cop
    csn
    #
    cdm
    #
    @7
    @10
    wf
    #
    wph
    @12
    cA
    csn
    #
    @7
    @10
    wf
    wph
    @13
    @9
    csn
    #
    @7
    @10
    wph
    cA
    @9
    cX
    @14
    upgr1e.a
    @9
    @14
    wcel
    wph
    @9
    cB
    cC
    prex
    #
    snid
    a1i
    fsnd
    #
    wph
    vx
    cB
    cC
    @5
    cV
    wph
    @9
    @4
    wss
    @9
    @5
    wcel
    wph
    @9
    cV
    @4
    wph
    cB
    cC
    cV
    upgr1e.b
    upgr1e.c
    prssd
    upgr1e.v
    syl6sseq
    @9
    @4
    @15
    elpw
    sylibr
    upgr1e.b
    upgr1elem
    fssd
    wph
    @11
    @13
    @7
    @10
    wph
    @13
    @3
    vx
    cvv
    @6
    cdif
    crab
    #
    @10
    wf
    @11
    @13
    wceq
    wph
    @13
    @14
    @17
    @10
    @16
    wph
    vx
    cB
    cC
    cvv
    cV
    @9
    cvv
    wcel
    wph
    @15
    a1i
    upgr1e.b
    upgr1elem
    fssd
    @13
    @17
    @10
    fdm
    syl
    feq2d
    mpbird
    wph
    @2
    @11
    @7
    @1
    @10
    upgr1e.e
    wph
    @1
    @10
    upgr1e.e
    dmeqd
    feq12d
    mpbird
    wph
    cB
    cV
    wcel
    cG
    cvv
    wcel
    @0
    @8
    wb
    upgr1e.b
    cG
    cB
    cV
    upgr1e.v
    1vgrex
    vx
    cvv
    @1
    cG
    @4
    @4
    eqid
    @1
    eqid
    isupgr
    3syl
    mpbird
end
