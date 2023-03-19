include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cprime.mm"
include "wnel.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cn.mm"
include "wcel.mm"
include "cfz.mm"
include "clcmf.mm"
include "cfv.mm"
include "cmpt.mm"
include "id.mm"
include "cmap.mm"
include "wf.mm"
include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "cc0.mm"
include "fzssz.mm"
include "a1i.mm"
include "fzfi.mm"
include "0nelfz1.mm"
include "lcmfn0cl.mm"
include "syl3anc.mm"
include "adantl.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "nnex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "cgcd.mm"
include "clt.mm"
include "c2.mm"
include "prmgaplcmlem2.mm"
include "cn0.mm"
include "eqidd.mm"
include "weq.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "simpl.mm"
include "lcmfcl.mm"
include "fvmptd.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "prmgaplem8.mm"
include "rgen.mm"

theorem prmgaplcm
  let vz: setvar z
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let vi: setvar i
  let vx: setvar x

  disjoint n p
  disjoint n q
  disjoint n z
  disjoint p q
  disjoint p z
  disjoint q z
  disjoint i n
  disjoint i p
  disjoint i q
  disjoint i x
  disjoint i z
  disjoint n x
  disjoint p x
  disjoint q x
  disjoint x z
  assert |- A. n e. NN E. p e. Prime E. q e. Prime ( n <_ ( q - p ) /\ A. z e. ( ( p + 1 ) ..^ q ) z e/ Prime )

  proof
    vn
    cv
    #
    vq
    cv
    #
    vp
    cv
    #
    cmin
    co
    cle
    wbr
    vz
    cv
    cprime
    wnel
    vz
    @2
    c1
    caddc
    co
    @1
    cfzo
    co
    wral
    wa
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    vn
    cn
    @0
    cn
    wcel
    #
    vz
    vi
    vx
    cn
    c1
    vx
    cv
    #
    cfz
    co
    #
    clcmf
    cfv
    #
    cmpt
    #
    @0
    vq
    vp
    @3
    id
    @3
    @7
    cn
    cn
    cmap
    co
    wcel
    #
    cn
    cn
    @7
    wf
    #
    @3
    vx
    cn
    @6
    cn
    @7
    @4
    cn
    wcel
    #
    @6
    cn
    wcel
    #
    @3
    @10
    @5
    cz
    wss
    #
    @5
    cfn
    wcel
    #
    cc0
    @5
    wnel
    #
    @11
    @12
    @10
    c1
    @4
    fzssz
    a1i
    @13
    @10
    c1
    @4
    fzfi
    a1i
    @14
    @10
    @4
    0nelfz1
    a1i
    @5
    lcmfn0cl
    syl3anc
    adantl
    @7
    eqid
    fmptd
    cn
    cvv
    wcel
    #
    @15
    wa
    @8
    @9
    wb
    @3
    @15
    @15
    nnex
    nnex
    pm3.2i
    cn
    cn
    @7
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    @3
    c1
    @0
    @7
    cfv
    #
    vi
    cv
    #
    caddc
    co
    #
    @17
    cgcd
    co
    #
    clt
    wbr
    vi
    c2
    @0
    cfz
    co
    #
    @3
    @17
    @20
    wcel
    #
    wa
    #
    c1
    c1
    @0
    cfz
    co
    #
    clcmf
    cfv
    #
    @17
    caddc
    co
    #
    @17
    cgcd
    co
    @19
    clt
    @17
    @0
    prmgaplcmlem2
    @22
    @18
    @25
    @17
    cgcd
    @22
    @16
    @24
    @17
    caddc
    @22
    vx
    @0
    @6
    @24
    cn
    @7
    cn0
    @22
    @7
    eqidd
    vx
    vn
    weq
    #
    @6
    @24
    wceq
    @22
    @26
    @5
    @23
    clcmf
    @4
    @0
    c1
    cfz
    oveq2
    fveq2d
    adantl
    @3
    @21
    simpl
    @23
    cz
    wss
    #
    @23
    cfn
    wcel
    #
    wa
    @24
    cn0
    wcel
    @22
    @27
    @28
    c1
    @0
    fzssz
    c1
    @0
    fzfi
    pm3.2i
    @23
    lcmfcl
    mp1i
    fvmptd
    oveq1d
    oveq1d
    breqtrrd
    ralrimiva
    prmgaplem8
    rgen
end
