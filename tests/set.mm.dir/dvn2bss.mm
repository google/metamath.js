include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "w3a.mm"
include "cdvn.mm"
include "cfv.mm"
include "cdm.mm"
include "cmin.mm"
include "caddc.mm"
include "cn0.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "elfznn0.mm"
include "3ad2ant3.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "uznn0sub.mm"
include "syl.mm"
include "dvnadd.mm"
include "syl22anc.mm"
include "nn0cnd.mm"
include "elfzuz2.mm"
include "nn0uz.mm"
include "syl6eleqr.mm"
include "pncan3d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "wss.mm"
include "cvv.mm"
include "wf.mm"
include "cnex.mm"
include "a1i.mm"
include "dvnf.mm"
include "syl3an3.mm"
include "dvnbss.mm"
include "wa.mm"
include "elpmi.mm"
include "3ad2ant2.mm"
include "simprd.mm"
include "sstrd.mm"
include "elpm2r.mm"
include "syl3anc.mm"
include "eqsstr3d.mm"

theorem dvn2bss
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let vs: setvar s


  assert |- ( ( S e. { RR , CC } /\ F e. ( CC ^pm S ) /\ M e. ( 0 ... N ) ) -> dom ( ( S Dn F ) ` N ) C_ dom ( ( S Dn F ) ` M ) )

  proof
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    #
    wcel
    #
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    w3a
    #
    cN
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    cdm
    cN
    cM
    cmin
    co
    #
    cS
    cM
    @6
    cfv
    #
    cdvn
    co
    cfv
    #
    cdm
    #
    @9
    cdm
    #
    @5
    @10
    @7
    @5
    @10
    cM
    @8
    caddc
    co
    #
    @6
    cfv
    #
    @7
    @5
    @1
    @3
    cM
    cn0
    wcel
    #
    @8
    cn0
    wcel
    #
    @10
    @14
    wceq
    @1
    @3
    @4
    simp1
    #
    @1
    @3
    @4
    simp2
    @4
    @1
    @15
    @3
    cM
    cN
    elfznn0
    #
    3ad2ant3
    #
    @5
    cN
    cM
    cuz
    cfv
    wcel
    #
    @16
    @4
    @1
    @20
    @3
    cM
    cc0
    cN
    elfzuz3
    3ad2ant3
    cM
    cN
    uznn0sub
    syl
    #
    cS
    cF
    cM
    @8
    dvnadd
    syl22anc
    @5
    @13
    cN
    @6
    @5
    cM
    cN
    @5
    cM
    @19
    nn0cnd
    @5
    cN
    @5
    cN
    cc0
    cuz
    cfv
    #
    cn0
    @4
    @1
    cN
    @22
    wcel
    @3
    cM
    cc0
    cN
    elfzuz2
    3ad2ant3
    nn0uz
    syl6eleqr
    nn0cnd
    pncan3d
    fveq2d
    eqtrd
    dmeqd
    @5
    @1
    @9
    @2
    wcel
    #
    @16
    @11
    @12
    wss
    @17
    @5
    cc
    cvv
    wcel
    #
    @1
    @12
    cc
    @9
    wf
    #
    @12
    cS
    wss
    @23
    @24
    @5
    cnex
    a1i
    @17
    @4
    @1
    @3
    @15
    @25
    @18
    cS
    cF
    cM
    dvnf
    syl3an3
    @5
    @12
    cF
    cdm
    #
    cS
    @4
    @1
    @3
    @15
    @12
    @26
    wss
    @18
    cS
    cF
    cM
    dvnbss
    syl3an3
    @5
    @26
    cc
    cF
    wf
    #
    @26
    cS
    wss
    #
    @3
    @1
    @27
    @28
    wa
    @4
    cc
    cS
    cF
    elpmi
    3ad2ant2
    simprd
    sstrd
    cc
    cS
    @12
    @9
    cvv
    @0
    elpm2r
    syl22anc
    @21
    cS
    @9
    @8
    dvnbss
    syl3anc
    eqsstr3d
end
