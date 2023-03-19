include "cuspgr.mm"
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
include "wf1.mm"
include "cpr.mm"
include "cop.mm"
include "wss.mm"
include "prex.mm"
include "snid.mm"
include "f1sng.mm"
include "sylancl.mm"
include "prssd.mm"
include "syl6sseq.mm"
include "elpw.mm"
include "sylibr.mm"
include "upgr1elem.mm"
include "f1ss.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wceq.mm"
include "wb.mm"
include "a1i.mm"
include "f1dm.mm"
include "f1eq2.mm"
include "3syl.mm"
include "mpbird.mm"
include "dmeqd.mm"
include "eqidd.mm"
include "f1eq123d.mm"
include "1vgrex.mm"
include "eqid.mm"
include "isuspgr.mm"

theorem uspgr1e
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume uspgr1e.v: |- V = ( Vtx ` G )
  assume uspgr1e.a: |- ( ph -> A e. X )
  assume uspgr1e.b: |- ( ph -> B e. V )
  assume uspgr1e.c: |- ( ph -> C e. V )
  assume uspgr1e.e: |- ( ph -> ( iEdg ` G ) = { <. A , { B , C } >. } )


  assert |- ( ph -> G e. USPGraph )

  proof
    wph
    cG
    cuspgr
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
    wf1
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
    wf1
    #
    wph
    @12
    cA
    csn
    #
    @7
    @10
    wf1
    #
    wph
    @13
    @9
    csn
    #
    @10
    wf1
    #
    @15
    @7
    wss
    @14
    wph
    cA
    cX
    wcel
    @9
    @15
    wcel
    @16
    uspgr1e.a
    @9
    cB
    cC
    prex
    #
    snid
    cA
    @9
    cX
    @15
    f1sng
    sylancl
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
    uspgr1e.b
    uspgr1e.c
    prssd
    uspgr1e.v
    syl6sseq
    @9
    @4
    @17
    elpw
    sylibr
    uspgr1e.b
    upgr1elem
    @13
    @15
    @7
    @10
    f1ss
    syl2anc
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
    wf1
    #
    @11
    @13
    wceq
    @12
    @14
    wb
    wph
    @16
    @15
    @19
    wss
    @20
    @18
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
    @17
    a1i
    uspgr1e.b
    upgr1elem
    @13
    @15
    @19
    @10
    f1ss
    syl2anc
    @13
    @19
    @10
    f1dm
    @11
    @13
    @7
    @10
    f1eq2
    3syl
    mpbird
    wph
    @2
    @11
    @7
    @7
    @1
    @10
    uspgr1e.e
    wph
    @1
    @10
    uspgr1e.e
    dmeqd
    wph
    @7
    eqidd
    f1eq123d
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
    uspgr1e.b
    cG
    cB
    cV
    uspgr1e.v
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
    isuspgr
    3syl
    mpbird
end
