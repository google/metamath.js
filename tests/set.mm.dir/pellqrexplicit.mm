include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "cpell1qr.mm"
include "cr.mm"
include "cv.mm"
include "wrex.mm"
include "nn0re.mm"
include "3ad2ant2.mm"
include "eldifi.mm"
include "3ad2ant1.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "3ad2ant3.mm"
include "remulcld.mm"
include "readdcld.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "eqidd.mm"
include "simpr.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "wb.mm"
include "elpell1qr.mm"
include "mpbir2and.mm"

theorem pellqrexplicit
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( D e. ( NN \ []NN ) /\ A e. NN0 /\ B e. NN0 ) /\ ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = 1 ) -> ( A + ( ( sqrt ` D ) x. B ) ) e. ( Pell1QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    w3a
    #
    cA
    c2
    cexp
    co
    #
    cD
    cB
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    #
    cA
    cD
    csqrt
    cfv
    #
    cB
    cmul
    co
    #
    caddc
    co
    #
    cD
    cpell1qr
    cfv
    wcel
    #
    @12
    cr
    wcel
    #
    @12
    va
    cv
    #
    @10
    vb
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @15
    c2
    cexp
    co
    #
    cD
    @16
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    #
    vb
    cn0
    wrex
    va
    cn0
    wrex
    #
    @3
    @14
    @8
    @3
    cA
    @11
    @1
    @0
    cA
    cr
    wcel
    @2
    cA
    nn0re
    3ad2ant2
    @3
    @10
    cB
    @3
    @10
    @3
    cD
    @3
    cD
    @0
    @1
    cD
    cn
    wcel
    @2
    cD
    cn
    csquarenn
    eldifi
    3ad2ant1
    nnrpd
    rpsqrtcld
    rpred
    @2
    @0
    cB
    cr
    wcel
    @1
    cB
    nn0re
    3ad2ant3
    remulcld
    readdcld
    adantr
    @9
    @1
    @2
    @12
    @12
    wceq
    #
    @8
    @26
    @0
    @1
    @2
    @8
    simpl2
    @0
    @1
    @2
    @8
    simpl3
    @9
    @12
    eqidd
    @3
    @8
    simpr
    @25
    @27
    @8
    wa
    @12
    cA
    @17
    caddc
    co
    #
    wceq
    #
    @4
    @22
    cmin
    co
    #
    c1
    wceq
    #
    wa
    va
    vb
    cA
    cB
    cn0
    cn0
    @15
    cA
    wceq
    #
    @19
    @29
    @24
    @31
    @32
    @18
    @28
    @12
    @15
    cA
    @17
    caddc
    oveq1
    eqeq2d
    @32
    @23
    @30
    c1
    @32
    @20
    @4
    @22
    cmin
    @15
    cA
    c2
    cexp
    oveq1
    oveq1d
    eqeq1d
    anbi12d
    @16
    cB
    wceq
    #
    @29
    @27
    @31
    @8
    @33
    @28
    @12
    @12
    @33
    @17
    @11
    cA
    caddc
    @16
    cB
    @10
    cmul
    oveq2
    oveq2d
    eqeq2d
    @33
    @30
    @7
    c1
    @33
    @22
    @6
    @4
    cmin
    @33
    @21
    @5
    cD
    cmul
    @16
    cB
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq1d
    anbi12d
    rspc2ev
    syl112anc
    @3
    @13
    @14
    @26
    wa
    wb
    #
    @8
    @0
    @1
    @34
    @2
    va
    vb
    @12
    cD
    elpell1qr
    3ad2ant1
    adantr
    mpbir2and
end
