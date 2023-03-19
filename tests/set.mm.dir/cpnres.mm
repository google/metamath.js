include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "ccpn.mm"
include "cfv.mm"
include "wa.mm"
include "cres.mm"
include "cpm.mm"
include "co.mm"
include "cdvn.mm"
include "cdm.mm"
include "ccncf.mm"
include "simpl.mm"
include "simpr.mm"
include "wss.mm"
include "cn0.mm"
include "wb.mm"
include "ssid.mm"
include "elfvdm.mm"
include "adantl.mm"
include "wfn.mm"
include "wceq.mm"
include "fncpn.mm"
include "ax-mp.mm"
include "fndm.mm"
include "mp1i.mm"
include "eleqtrd.mm"
include "elcpn.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simpld.mm"
include "pmresg.mm"
include "syl2anc.mm"
include "wf.mm"
include "simprd.mm"
include "cncff.mm"
include "syl.mm"
include "fdm.mm"
include "dvnres.mm"
include "syl31anc.mm"
include "cin.mm"
include "resres.mm"
include "rescom.mm"
include "eqtr3i.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "syl5eq.mm"
include "inss2.mm"
include "rescncf.mm"
include "mpsyl.mm"
include "eqeltrrd.mm"
include "dmres.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"
include "recnprss.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem cpnres
  let cS: class S
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let cM: class M
  let vs: setvar s


  assert |- ( ( S e. { RR , CC } /\ F e. ( ( C^n ` CC ) ` N ) ) -> ( F |` S ) e. ( ( C^n ` S ) ` N ) )

  proof
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cN
    cc
    ccpn
    cfv
    #
    cfv
    wcel
    #
    wa
    #
    cF
    cS
    cres
    #
    cN
    cS
    ccpn
    cfv
    cfv
    wcel
    #
    @5
    cc
    cS
    cpm
    co
    wcel
    #
    cN
    cS
    @5
    cdvn
    co
    cfv
    #
    @5
    cdm
    #
    cc
    ccncf
    co
    #
    wcel
    #
    @4
    @1
    cF
    cc
    cc
    cpm
    co
    wcel
    #
    @7
    @1
    @3
    simpl
    #
    @4
    @12
    cN
    cc
    cF
    cdvn
    co
    cfv
    #
    cF
    cdm
    #
    cc
    ccncf
    co
    wcel
    #
    @4
    @3
    @12
    @16
    wa
    #
    @1
    @3
    simpr
    @4
    cc
    cc
    wss
    #
    cN
    cn0
    wcel
    #
    @3
    @17
    wb
    cc
    ssid
    #
    @4
    cN
    @2
    cdm
    #
    cn0
    @3
    cN
    @21
    wcel
    @1
    cF
    cN
    @2
    elfvdm
    adantl
    @2
    cn0
    wfn
    #
    @21
    cn0
    wceq
    @4
    @18
    @22
    @20
    cc
    fncpn
    ax-mp
    cn0
    @2
    fndm
    mp1i
    eleqtrd
    #
    cc
    cF
    cN
    elcpn
    sylancr
    mpbid
    #
    simpld
    #
    cc
    cS
    cc
    cF
    @0
    pmresg
    syl2anc
    @4
    @8
    @14
    cS
    cres
    #
    @10
    @4
    @1
    @12
    @19
    @14
    cdm
    @15
    wceq
    #
    @8
    @26
    wceq
    @13
    @25
    @23
    @4
    @15
    cc
    @14
    wf
    #
    @27
    @4
    @16
    @28
    @4
    @12
    @16
    @24
    simprd
    #
    @15
    cc
    @14
    cncff
    syl
    #
    @15
    cc
    @14
    fdm
    syl
    cS
    cF
    cN
    dvnres
    syl31anc
    @4
    @26
    cS
    @15
    cin
    #
    cc
    ccncf
    co
    #
    @10
    @4
    @14
    @31
    cres
    #
    @26
    @32
    @4
    @33
    @14
    @15
    cres
    #
    cS
    cres
    #
    @26
    @26
    @15
    cres
    @33
    @35
    @14
    cS
    @15
    resres
    @14
    cS
    @15
    rescom
    eqtr3i
    @4
    @34
    @14
    cS
    @4
    @28
    @14
    @15
    wfn
    @34
    @14
    wceq
    @30
    @15
    cc
    @14
    ffn
    @15
    @14
    fnresdm
    3syl
    reseq1d
    syl5eq
    @31
    @15
    wss
    @4
    @16
    @33
    @32
    wcel
    cS
    @15
    inss2
    @29
    @15
    cc
    @31
    @14
    rescncf
    mpsyl
    eqeltrrd
    @9
    @31
    cc
    ccncf
    cF
    cS
    dmres
    oveq1i
    syl6eleqr
    eqeltrd
    @4
    cS
    cc
    wss
    #
    @19
    @6
    @7
    @11
    wa
    wb
    @1
    @36
    @3
    cS
    recnprss
    adantr
    @23
    cS
    @5
    cN
    elcpn
    syl2anc
    mpbir2and
end
