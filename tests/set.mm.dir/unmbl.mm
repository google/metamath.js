include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "mblss.mm"
include "anim12i.mm"
include "unss.mm"
include "sylib.mm"
include "elpwi.mm"
include "inss1.mm"
include "ovolsscl.mm"
include "mp3an1.mm"
include "adantl.mm"
include "difss.mm"
include "simprl.mm"
include "syl5ss.mm"
include "syl2anc.mm"
include "readdcld.mm"
include "incom.mm"
include "indifcom.mm"
include "eqtri.mm"
include "uneq2i.mm"
include "indi.mm"
include "undif2.mm"
include "ineq2i.mm"
include "3eqtr2ri.mm"
include "fveq2i.mm"
include "ovolun.mm"
include "syl22anc.mm"
include "syl5eqbr.mm"
include "leadd1dd.mm"
include "wceq.mm"
include "simplr.mm"
include "mblsplit.mm"
include "syl3anc.mm"
include "difun1.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "simpll.mm"
include "simprr.mm"
include "recnd.mm"
include "addassd.mm"
include "3eqtr4d.mm"
include "breqtrrd.mm"
include "expr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "ismbl2.mm"
include "sylanbrc.mm"

theorem unmbl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. dom vol /\ B e. dom vol ) -> ( A u. B ) e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    cun
    #
    cr
    wss
    #
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @6
    @4
    cin
    #
    covol
    cfv
    #
    @6
    @4
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @7
    cle
    wbr
    #
    wi
    #
    vx
    cr
    cpw
    #
    wral
    @4
    @0
    wcel
    @3
    cA
    cr
    wss
    #
    cB
    cr
    wss
    #
    wa
    @5
    @1
    @17
    @2
    @18
    cA
    mblss
    cB
    mblss
    anim12i
    cA
    cB
    cr
    unss
    sylib
    @3
    @15
    vx
    @16
    @6
    @16
    wcel
    @3
    @6
    cr
    wss
    #
    @15
    @6
    cr
    elpwi
    @3
    @19
    @8
    @14
    @3
    @19
    @8
    wa
    #
    wa
    #
    @13
    @6
    cA
    cin
    #
    covol
    cfv
    #
    @6
    cA
    cdif
    #
    cB
    cin
    #
    covol
    cfv
    #
    caddc
    co
    #
    @12
    caddc
    co
    #
    @7
    cle
    @21
    @10
    @27
    @12
    @20
    @10
    cr
    wcel
    #
    @3
    @9
    @6
    wss
    @19
    @8
    @29
    @6
    @4
    inss1
    @9
    @6
    ovolsscl
    mp3an1
    adantl
    @21
    @23
    @26
    @20
    @23
    cr
    wcel
    #
    @3
    @22
    @6
    wss
    @19
    @8
    @30
    @6
    cA
    inss1
    #
    @22
    @6
    ovolsscl
    mp3an1
    adantl
    #
    @21
    @24
    cr
    wss
    #
    @24
    covol
    cfv
    #
    cr
    wcel
    #
    @26
    cr
    wcel
    #
    @21
    @24
    @6
    cr
    @6
    cA
    difss
    #
    @3
    @19
    @8
    simprl
    #
    syl5ss
    #
    @20
    @35
    @3
    @24
    @6
    wss
    @19
    @8
    @35
    @37
    @24
    @6
    ovolsscl
    mp3an1
    adantl
    #
    @25
    @24
    wss
    @33
    @35
    @36
    @24
    cB
    inss1
    #
    @25
    @24
    ovolsscl
    mp3an1
    syl2anc
    #
    readdcld
    @20
    @12
    cr
    wcel
    #
    @3
    @11
    @6
    wss
    @19
    @8
    @43
    @6
    @4
    difss
    @11
    @6
    ovolsscl
    mp3an1
    adantl
    #
    @21
    @10
    @22
    @25
    cun
    #
    covol
    cfv
    #
    @27
    cle
    @9
    @45
    covol
    @45
    @22
    @6
    cB
    cA
    cdif
    #
    cin
    #
    cun
    @6
    cA
    @47
    cun
    #
    cin
    @9
    @25
    @48
    @22
    @25
    cB
    @24
    cin
    @48
    @24
    cB
    incom
    cB
    @6
    cA
    indifcom
    eqtri
    uneq2i
    @6
    cA
    @47
    indi
    @49
    @4
    @6
    cA
    cB
    undif2
    ineq2i
    3eqtr2ri
    fveq2i
    @21
    @22
    cr
    wss
    @30
    @25
    cr
    wss
    @36
    @46
    @27
    cle
    wbr
    @21
    @22
    @6
    cr
    @31
    @38
    syl5ss
    @32
    @21
    @25
    @24
    cr
    @41
    @39
    syl5ss
    @42
    @22
    @25
    ovolun
    syl22anc
    syl5eqbr
    leadd1dd
    @21
    @23
    @34
    caddc
    co
    #
    @23
    @26
    @12
    caddc
    co
    #
    caddc
    co
    @7
    @28
    @21
    @34
    @51
    @23
    caddc
    @21
    @34
    @26
    @24
    cB
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @51
    @21
    @2
    @33
    @35
    @34
    @54
    wceq
    @1
    @2
    @20
    simplr
    @39
    @40
    cB
    @24
    mblsplit
    syl3anc
    @12
    @53
    @26
    caddc
    @11
    @52
    covol
    @6
    cA
    cB
    difun1
    fveq2i
    oveq2i
    syl6eqr
    oveq2d
    @21
    @1
    @19
    @8
    @7
    @50
    wceq
    @1
    @2
    @20
    simpll
    @38
    @3
    @19
    @8
    simprr
    cA
    @6
    mblsplit
    syl3anc
    @21
    @23
    @26
    @12
    @21
    @23
    @32
    recnd
    @21
    @26
    @42
    recnd
    @21
    @12
    @44
    recnd
    addassd
    3eqtr4d
    breqtrrd
    expr
    sylan2
    ralrimiva
    vx
    @4
    ismbl2
    sylanbrc
end
