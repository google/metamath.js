include "cn.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "csup.mm"
include "nnuz.mm"
include "1zzd.mm"
include "rge0ssre.mm"
include "fss.mm"
include "mpan2.mm"
include "ffvelrnda.mm"
include "serfre.mm"
include "frn.mm"
include "syl.mm"
include "adantr.mm"
include "1nn.mm"
include "fdm.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "3syl.mm"
include "cfv.mm"
include "climdm.mm"
include "biimpi.mm"
include "adantl.mm"
include "climrecl.mm"
include "simpr.mm"
include "simplll.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "sylancom.mm"
include "elrege0.mm"
include "simprbi.mm"
include "adantlr.mm"
include "climserle.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "suprcl.mm"
include "syl3anc.mm"

theorem rge0scvg
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z


  assert |- ( ( F : NN --> ( 0 [,) +oo ) /\ seq 1 ( + , F ) e. dom ~~> ) -> sup ( ran seq 1 ( + , F ) , RR , < ) e. RR )

  proof
    cn
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    caddc
    cF
    c1
    cseq
    #
    cli
    cdm
    wcel
    #
    wa
    #
    @2
    crn
    #
    cr
    wss
    #
    @5
    c0
    wne
    #
    vz
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vz
    @5
    wral
    #
    vx
    cr
    wrex
    #
    @5
    cr
    clt
    csup
    cr
    wcel
    @1
    @6
    @3
    @1
    cn
    cr
    @2
    wf
    #
    @6
    @1
    vj
    cF
    c1
    cn
    nnuz
    @1
    1zzd
    @1
    cn
    cr
    vj
    cv
    #
    cF
    @1
    @0
    cr
    wss
    cn
    cr
    cF
    wf
    rge0ssre
    cn
    @0
    cr
    cF
    fss
    mpan2
    ffvelrnda
    serfre
    #
    cn
    cr
    @2
    frn
    syl
    adantr
    @1
    @7
    @3
    @1
    @13
    c1
    @2
    cdm
    #
    wcel
    #
    @7
    @15
    @13
    c1
    cn
    @16
    1nn
    cn
    cr
    @2
    fdm
    syl5eleqr
    @17
    @16
    c0
    wne
    @7
    @16
    c1
    ne0i
    @16
    c0
    @5
    c0
    @2
    dm0rn0
    necon3bii
    sylib
    3syl
    adantr
    @4
    @12
    vk
    cv
    #
    @2
    cfv
    #
    @9
    cle
    wbr
    #
    vk
    cn
    wral
    #
    vx
    cr
    wrex
    #
    @4
    @2
    cli
    cfv
    #
    cr
    wcel
    @19
    @23
    cle
    wbr
    #
    vk
    cn
    wral
    #
    @22
    @4
    @23
    vk
    @2
    c1
    cn
    nnuz
    @4
    1zzd
    @3
    @2
    @23
    cli
    wbr
    #
    @1
    @3
    @26
    @2
    climdm
    biimpi
    adantl
    #
    @4
    cn
    cr
    @18
    @2
    @1
    @13
    @3
    @15
    adantr
    ffvelrnda
    climrecl
    @4
    @24
    vk
    cn
    @4
    @18
    cn
    wcel
    #
    wa
    #
    @23
    vj
    cF
    c1
    @18
    cn
    nnuz
    @4
    @28
    simpr
    @4
    @26
    @28
    @27
    adantr
    @29
    @14
    cn
    wcel
    #
    @1
    @14
    cF
    cfv
    #
    cr
    wcel
    #
    @1
    @3
    @28
    @30
    simplll
    @1
    @30
    wa
    #
    @0
    cr
    @31
    rge0ssre
    cn
    @0
    @14
    cF
    ffvelrn
    #
    sseldi
    sylancom
    @4
    @30
    cc0
    @31
    cle
    wbr
    #
    @28
    @1
    @30
    @35
    @3
    @33
    @31
    @0
    wcel
    #
    @35
    @34
    @36
    @32
    @35
    @31
    elrege0
    simprbi
    syl
    adantlr
    adantlr
    climserle
    ralrimiva
    @21
    @25
    vx
    @23
    cr
    @9
    @23
    wceq
    @20
    @24
    vk
    cn
    @9
    @23
    @19
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    @1
    @12
    @22
    wb
    @3
    @1
    @11
    @21
    vx
    cr
    @1
    @13
    @2
    cn
    wfn
    @11
    @21
    wb
    @15
    cn
    cr
    @2
    ffn
    @10
    @20
    vz
    vk
    cn
    @2
    @8
    @19
    @9
    cle
    breq1
    ralrn
    3syl
    rexbidv
    adantr
    mpbird
    vx
    vz
    @5
    suprcl
    syl3anc
end
