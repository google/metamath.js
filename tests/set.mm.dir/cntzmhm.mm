include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "cima.mm"
include "cbs.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "wf.mm"
include "eqid.mm"
include "mhmf.mm"
include "cntzssv.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "cntzi.mm"
include "adantll.mm"
include "fveq2d.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "cvv.mm"
include "wss.mm"
include "cntzrcl.mm"
include "adantl.mm"
include "simprd.mm"
include "sselda.mm"
include "mhmlin.mm"
include "syl3anc.mm"
include "3eqtr3d.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "adantr.mm"
include "ffn.mm"
include "syl.mm"
include "oveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "ralima.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "elcntz.mm"
include "mpbir2and.mm"

theorem cntzmhm
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume cntzmhm.z: |- Z = ( Cntz ` G )
  assume cntzmhm.y: |- Y = ( Cntz ` H )


  assert |- ( ( F e. ( G MndHom H ) /\ A e. ( Z ` S ) ) -> ( F ` A ) e. ( Y ` ( F " S ) ) )

  proof
    cF
    cG
    cH
    cmhm
    co
    wcel
    #
    cA
    cS
    cZ
    cfv
    #
    wcel
    #
    wa
    #
    cA
    cF
    cfv
    #
    cF
    cS
    cima
    #
    cY
    cfv
    wcel
    #
    @4
    cH
    cbs
    cfv
    #
    wcel
    #
    @4
    vy
    cv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    @9
    @4
    @10
    co
    #
    wceq
    #
    vy
    @5
    wral
    #
    @0
    cG
    cbs
    cfv
    #
    @7
    cF
    wf
    #
    cA
    @15
    wcel
    #
    @8
    @2
    @15
    @7
    cG
    cH
    cF
    @15
    eqid
    #
    @7
    eqid
    #
    mhmf
    #
    @1
    @15
    cA
    @15
    cS
    cG
    cZ
    @18
    cntzmhm.z
    cntzssv
    sseli
    #
    @15
    @7
    cA
    cF
    ffvelrn
    syl2an
    @3
    @14
    @4
    vx
    cv
    #
    cF
    cfv
    #
    @10
    co
    #
    @23
    @4
    @10
    co
    #
    wceq
    #
    vx
    cS
    wral
    #
    @3
    @26
    vx
    cS
    @3
    @22
    cS
    wcel
    #
    wa
    #
    cA
    @22
    cG
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @22
    cA
    @30
    co
    #
    cF
    cfv
    #
    @24
    @25
    @29
    @31
    @33
    cF
    @2
    @28
    @31
    @33
    wceq
    @0
    @30
    cS
    cG
    cA
    @22
    cZ
    @30
    eqid
    #
    cntzmhm.z
    cntzi
    adantll
    fveq2d
    @29
    @0
    @17
    @22
    @15
    wcel
    #
    @32
    @24
    wceq
    @0
    @2
    @28
    simpll
    #
    @2
    @17
    @0
    @28
    @21
    ad2antlr
    #
    @3
    cS
    @15
    @22
    @3
    cG
    cvv
    wcel
    #
    cS
    @15
    wss
    #
    @2
    @39
    @40
    wa
    @0
    @15
    cS
    cG
    cA
    cZ
    @18
    cntzmhm.z
    cntzrcl
    adantl
    simprd
    #
    sselda
    #
    @15
    @30
    @10
    cG
    cH
    cF
    cA
    @22
    @18
    @35
    @10
    eqid
    #
    mhmlin
    syl3anc
    @29
    @0
    @36
    @17
    @34
    @25
    wceq
    @37
    @42
    @38
    @15
    @30
    @10
    cG
    cH
    cF
    @22
    cA
    @18
    @35
    @43
    mhmlin
    syl3anc
    3eqtr3d
    ralrimiva
    @3
    cF
    @15
    wfn
    #
    @40
    @14
    @27
    wb
    @3
    @16
    @44
    @0
    @16
    @2
    @20
    adantr
    #
    @15
    @7
    cF
    ffn
    syl
    @41
    @13
    @26
    vy
    vx
    @15
    cS
    cF
    @9
    @23
    wceq
    @11
    @24
    @12
    @25
    @9
    @23
    @4
    @10
    oveq2
    @9
    @23
    @4
    @10
    oveq1
    eqeq12d
    ralima
    syl2anc
    mpbird
    @3
    @5
    @7
    wss
    @6
    @8
    @14
    wa
    wb
    @3
    @5
    cF
    crn
    #
    @7
    cF
    cS
    imassrn
    @3
    @16
    @46
    @7
    wss
    @45
    @15
    @7
    cF
    frn
    syl
    syl5ss
    vy
    @4
    @7
    @10
    @5
    cH
    cY
    @19
    @43
    cntzmhm.y
    elcntz
    syl
    mpbir2and
end
