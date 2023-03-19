include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "ccpn.mm"
include "cfv.mm"
include "wa.mm"
include "cc0.mm"
include "cdvn.mm"
include "co.mm"
include "cdm.mm"
include "ccncf.mm"
include "wss.mm"
include "cpm.mm"
include "wceq.mm"
include "recnprss.mm"
include "adantr.mm"
include "cn0.mm"
include "cuz.mm"
include "simpl.mm"
include "0nn0.mm"
include "a1i.mm"
include "elfvdm.mm"
include "adantl.mm"
include "wfn.mm"
include "fncpn.mm"
include "fndm.mm"
include "3syl.mm"
include "eleqtrd.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cpnord.mm"
include "syl3anc.mm"
include "simpr.mm"
include "sseldd.mm"
include "wb.mm"
include "elcpn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "dvn0.mm"
include "simprd.mm"
include "eqeltrrd.mm"

theorem cpncn
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


  assert |- ( ( S e. { RR , CC } /\ F e. ( ( C^n ` S ) ` N ) ) -> F e. ( dom F -cn-> CC ) )

  proof
    cS
    cr
    cc
    cpr
    wcel
    #
    cF
    cN
    cS
    ccpn
    cfv
    #
    cfv
    #
    wcel
    #
    wa
    #
    cc0
    cS
    cF
    cdvn
    co
    cfv
    #
    cF
    cF
    cdm
    cc
    ccncf
    co
    #
    @4
    cS
    cc
    wss
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    @5
    cF
    wceq
    @0
    @7
    @3
    cS
    recnprss
    adantr
    #
    @4
    @8
    @5
    @6
    wcel
    #
    @4
    cF
    cc0
    @1
    cfv
    #
    wcel
    #
    @8
    @10
    wa
    #
    @4
    @2
    @11
    cF
    @4
    @0
    cc0
    cn0
    wcel
    #
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @2
    @11
    wss
    @0
    @3
    simpl
    @14
    @4
    0nn0
    a1i
    #
    @4
    cN
    cn0
    @15
    @4
    cN
    @1
    cdm
    #
    cn0
    @3
    cN
    @17
    wcel
    @0
    cF
    cN
    @1
    elfvdm
    adantl
    @4
    @7
    @1
    cn0
    wfn
    @17
    cn0
    wceq
    @9
    cS
    fncpn
    cn0
    @1
    fndm
    3syl
    eleqtrd
    nn0uz
    syl6eleq
    cS
    cc0
    cN
    cpnord
    syl3anc
    @0
    @3
    simpr
    sseldd
    @4
    @7
    @14
    @12
    @13
    wb
    @9
    @16
    cS
    cF
    cc0
    elcpn
    syl2anc
    mpbid
    #
    simpld
    cS
    cF
    dvn0
    syl2anc
    @4
    @8
    @10
    @18
    simprd
    eqeltrrd
end
