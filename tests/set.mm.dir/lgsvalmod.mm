include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cneg.mm"
include "cmo.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "eldifi.mm"
include "adantl.mm"
include "prmz.mm"
include "syl.mm"
include "lgscl.mm"
include "syldan.mm"
include "zred.mm"
include "peano2re.mm"
include "cn0.mm"
include "cn.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "neg1rr.mm"
include "a1i.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "lgsval3.mm"
include "eqcomd.mm"
include "modcld.mm"
include "recnd.mm"
include "cc.mm"
include "ax-1cn.mm"
include "subadd2d.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "modabs2.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "modadd1.mm"
include "syl221anc.mm"
include "negsub.mm"
include "sylancl.mm"
include "pncan.mm"
include "3eqtr3d.mm"

theorem lgsvalmod
  let cA: class A
  let cP: class P
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cN: class N


  assert |- ( ( A e. ZZ /\ P e. ( Prime \ { 2 } ) ) -> ( ( A /L P ) mod P ) = ( ( A ^ ( ( P - 1 ) / 2 ) ) mod P ) )

  proof
    cA
    cz
    wcel
    #
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    wa
    #
    cA
    cP
    clgs
    co
    #
    c1
    caddc
    co
    #
    c1
    cneg
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    cA
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    @6
    caddc
    co
    #
    cP
    cmo
    co
    #
    @4
    cP
    cmo
    co
    @10
    cP
    cmo
    co
    @3
    @5
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    cP
    crp
    wcel
    #
    @5
    cP
    cmo
    co
    #
    @11
    cP
    cmo
    co
    #
    wceq
    @8
    @13
    wceq
    @3
    @4
    cr
    wcel
    @14
    @3
    @4
    @0
    @2
    cP
    cz
    wcel
    #
    @4
    cz
    wcel
    @3
    cP
    cprime
    wcel
    #
    @20
    @2
    @21
    @0
    cP
    cprime
    @1
    eldifi
    adantl
    #
    cP
    prmz
    syl
    cA
    cP
    lgscl
    syldan
    zred
    #
    @4
    peano2re
    syl
    #
    @3
    @10
    cr
    wcel
    @15
    @3
    @10
    @0
    @2
    @9
    cn0
    wcel
    @10
    cz
    wcel
    @3
    @9
    @2
    @9
    cn
    wcel
    @0
    cP
    oddprm
    adantl
    nnnn0d
    cA
    @9
    zexpcl
    syldan
    zred
    #
    @10
    peano2re
    syl
    #
    @16
    @3
    neg1rr
    a1i
    @3
    cP
    @3
    @21
    cP
    cn
    wcel
    @22
    cP
    prmnn
    syl
    nnrpd
    #
    @3
    @18
    @19
    cP
    cmo
    co
    #
    @19
    @3
    @5
    @19
    cP
    cmo
    @3
    @19
    c1
    cmin
    co
    #
    @4
    wceq
    @5
    @19
    wceq
    @3
    @4
    @29
    cA
    cP
    lgsval3
    eqcomd
    @3
    @19
    c1
    @4
    @3
    @19
    @3
    @11
    cP
    @26
    @27
    modcld
    recnd
    c1
    cc
    wcel
    #
    @3
    ax-1cn
    a1i
    @3
    @4
    @23
    recnd
    #
    subadd2d
    mpbid
    oveq1d
    @3
    @15
    @17
    @28
    @19
    wceq
    @26
    @27
    @11
    cP
    modabs2
    syl2anc
    eqtrd
    @5
    @11
    @6
    cP
    modadd1
    syl221anc
    @3
    @7
    @4
    cP
    cmo
    @3
    @7
    @5
    c1
    cmin
    co
    #
    @4
    @3
    @5
    cc
    wcel
    @30
    @7
    @32
    wceq
    @3
    @5
    @24
    recnd
    ax-1cn
    @5
    c1
    negsub
    sylancl
    @3
    @4
    cc
    wcel
    @30
    @32
    @4
    wceq
    @31
    ax-1cn
    @4
    c1
    pncan
    sylancl
    eqtrd
    oveq1d
    @3
    @12
    @10
    cP
    cmo
    @3
    @12
    @11
    c1
    cmin
    co
    #
    @10
    @3
    @11
    cc
    wcel
    @30
    @12
    @33
    wceq
    @3
    @11
    @26
    recnd
    ax-1cn
    @11
    c1
    negsub
    sylancl
    @3
    @10
    cc
    wcel
    @30
    @33
    @10
    wceq
    @3
    @10
    @25
    recnd
    ax-1cn
    @10
    c1
    pncan
    sylancl
    eqtrd
    oveq1d
    3eqtr3d
end
