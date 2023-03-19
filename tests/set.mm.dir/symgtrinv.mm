include "wcel.mm"
include "cword.mm"
include "wa.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "coppg.mm"
include "ccom.mm"
include "creverse.mm"
include "cmhm.mm"
include "cbs.mm"
include "wceq.mm"
include "cgrp.mm"
include "cgim.mm"
include "cghm.mm"
include "symggrp.mm"
include "eqid.mm"
include "invoppggim.mm"
include "gimghm.mm"
include "ghmmhm.mm"
include "4syl.mm"
include "wss.mm"
include "symgtrf.mm"
include "sswrd.mm"
include "ax-mp.mm"
include "sseli.mm"
include "gsumwmhm.mm"
include "syl2an.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wf.mm"
include "wfn.mm"
include "grpinvf.mm"
include "syl.mm"
include "adantr.mm"
include "wrdf.mm"
include "adantl.mm"
include "fss.mm"
include "sylancl.mm"
include "fco.mm"
include "syl2anc.mm"
include "ffn.mm"
include "cv.mm"
include "ccnv.mm"
include "fvco2.mm"
include "sylan.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "symginv.mm"
include "cpmtr.mm"
include "pmtrfcnv.mm"
include "3eqtrd.mm"
include "eqfnfvd.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "gsumwrev.mm"

theorem symgtrinv
  let cD: class D
  let cT: class T
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume symgtrinv.t: |- T = ran ( pmTrsp ` D )
  assume symgtrinv.g: |- G = ( SymGrp ` D )
  assume symgtrinv.i: |- I = ( invg ` G )


  assert |- ( ( D e. V /\ W e. Word T ) -> ( I ` ( G gsum W ) ) = ( G gsum ( reverse ` W ) ) )

  proof
    cD
    cV
    wcel
    #
    cW
    cT
    cword
    #
    wcel
    #
    wa
    #
    cG
    cW
    cgsu
    co
    cI
    cfv
    #
    cG
    coppg
    cfv
    #
    cI
    cW
    ccom
    #
    cgsu
    co
    #
    @5
    cW
    cgsu
    co
    #
    cG
    cW
    creverse
    cfv
    cgsu
    co
    #
    @0
    cI
    cG
    @5
    cmhm
    co
    wcel
    #
    cW
    cG
    cbs
    cfv
    #
    cword
    #
    wcel
    #
    @4
    @7
    wceq
    @2
    @0
    cG
    cgrp
    wcel
    #
    cI
    cG
    @5
    cgim
    co
    wcel
    cI
    cG
    @5
    cghm
    co
    wcel
    @10
    cD
    cG
    cV
    symgtrinv.g
    symggrp
    #
    cG
    cI
    @5
    @5
    eqid
    #
    symgtrinv.i
    invoppggim
    cG
    @5
    cI
    gimghm
    cG
    @5
    cI
    ghmmhm
    4syl
    @1
    @12
    cW
    cT
    @11
    wss
    #
    @1
    @12
    wss
    @11
    cD
    cT
    cG
    symgtrinv.t
    symgtrinv.g
    @11
    eqid
    #
    symgtrf
    #
    cT
    @11
    sswrd
    ax-mp
    sseli
    #
    @11
    cI
    cG
    @5
    cW
    @18
    gsumwmhm
    syl2an
    @3
    @6
    cW
    @5
    cgsu
    @3
    vx
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    @6
    cW
    @3
    @21
    @11
    @6
    wf
    #
    @6
    @21
    wfn
    @3
    @11
    @11
    cI
    wf
    #
    @21
    @11
    cW
    wf
    #
    @22
    @0
    @23
    @2
    @0
    @14
    @23
    @15
    @11
    cG
    cI
    @18
    symgtrinv.i
    grpinvf
    syl
    adantr
    @3
    @21
    cT
    cW
    wf
    #
    @17
    @24
    @2
    @25
    @0
    cT
    cW
    wrdf
    adantl
    #
    @19
    @21
    cT
    @11
    cW
    fss
    sylancl
    @21
    @11
    @11
    cI
    cW
    fco
    syl2anc
    @21
    @11
    @6
    ffn
    syl
    @3
    @25
    cW
    @21
    wfn
    #
    @26
    @21
    cT
    cW
    ffn
    syl
    #
    @3
    vx
    cv
    #
    @21
    wcel
    #
    wa
    #
    @29
    @6
    cfv
    #
    @29
    cW
    cfv
    #
    cI
    cfv
    #
    @33
    ccnv
    #
    @33
    @3
    @27
    @30
    @32
    @34
    wceq
    @28
    @21
    cI
    cW
    @29
    fvco2
    sylan
    @31
    @33
    @11
    wcel
    @34
    @35
    wceq
    @31
    cT
    @11
    @33
    @19
    @3
    @21
    cT
    @29
    cW
    @26
    ffvelrnda
    #
    sseldi
    cD
    @11
    @33
    cG
    cI
    symgtrinv.g
    @18
    symgtrinv.i
    symginv
    syl
    @31
    @33
    cT
    wcel
    @35
    @33
    wceq
    @36
    cD
    cT
    cD
    cpmtr
    cfv
    #
    @33
    @37
    eqid
    symgtrinv.t
    pmtrfcnv
    syl
    3eqtrd
    eqfnfvd
    oveq2d
    @0
    cG
    cmnd
    wcel
    #
    @13
    @8
    @9
    wceq
    @2
    @0
    @14
    @38
    @15
    cG
    grpmnd
    syl
    @20
    @11
    cG
    @5
    cW
    @18
    @16
    gsumwrev
    syl2an
    3eqtrd
end
