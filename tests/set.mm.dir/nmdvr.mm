include "cnrg.mm"
include "wcel.mm"
include "cnzr.mm"
include "wa.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "cmul.mm"
include "wceq.mm"
include "simpll.mm"
include "simprl.mm"
include "crg.mm"
include "nrgring.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "eqid.mm"
include "ringinvcl.mm"
include "syl2anc.mm"
include "nmmul.mm"
include "syl3anc.mm"
include "simplr.mm"
include "nminvr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "dvrval.mm"
include "adantl.mm"
include "fveq2d.mm"
include "cngp.mm"
include "cr.mm"
include "nrgngp.mm"
include "nmcl.mm"
include "recnd.mm"
include "unitss.mm"
include "sseldi.mm"
include "cc0.mm"
include "wne.mm"
include "unitnmn0.mm"
include "3expa.mm"
include "adantrl.mm"
include "divrecd.mm"
include "3eqtr4d.mm"

theorem nmdvr
  let cA: class A
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cU: class U
  let cN: class N
  let cX: class X
  assume nmdvr.x: |- X = ( Base ` R )
  assume nmdvr.n: |- N = ( norm ` R )
  assume nmdvr.u: |- U = ( Unit ` R )
  assume nmdvr.d: |- ./ = ( /r ` R )


  assert |- ( ( ( R e. NrmRing /\ R e. NzRing ) /\ ( A e. X /\ B e. U ) ) -> ( N ` ( A ./ B ) ) = ( ( N ` A ) / ( N ` B ) ) )

  proof
    cR
    cnrg
    wcel
    #
    cR
    cnzr
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cU
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cR
    cinvr
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cN
    cfv
    #
    cA
    cN
    cfv
    #
    c1
    cB
    cN
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cA
    cB
    c.dv
    co
    #
    cN
    cfv
    @12
    @13
    cdiv
    co
    @6
    @11
    @12
    @8
    cN
    cfv
    #
    cmul
    co
    #
    @15
    @6
    @0
    @3
    @8
    cX
    wcel
    #
    @11
    @18
    wceq
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    @6
    cR
    crg
    wcel
    #
    @4
    @19
    @0
    @22
    @1
    @5
    cR
    nrgring
    ad2antrr
    @2
    @3
    @4
    simprr
    #
    cX
    cR
    cU
    @7
    cB
    nmdvr.u
    @7
    eqid
    #
    nmdvr.x
    ringinvcl
    syl2anc
    cA
    @8
    cR
    @9
    cN
    cX
    nmdvr.x
    nmdvr.n
    @9
    eqid
    #
    nmmul
    syl3anc
    @6
    @17
    @14
    @12
    cmul
    @6
    @0
    @1
    @4
    @17
    @14
    wceq
    @20
    @0
    @1
    @5
    simplr
    @23
    cB
    cR
    cU
    @7
    cN
    nmdvr.n
    nmdvr.u
    @24
    nminvr
    syl3anc
    oveq2d
    eqtrd
    @6
    @16
    @10
    cN
    @5
    @16
    @10
    wceq
    @2
    cX
    c.dv
    cR
    @9
    cU
    @7
    cA
    cB
    nmdvr.x
    @25
    nmdvr.u
    @24
    nmdvr.d
    dvrval
    adantl
    fveq2d
    @6
    @12
    @13
    @6
    @12
    @6
    cR
    cngp
    wcel
    #
    @3
    @12
    cr
    wcel
    @0
    @26
    @1
    @5
    cR
    nrgngp
    ad2antrr
    #
    @21
    cA
    cR
    cN
    cX
    nmdvr.x
    nmdvr.n
    nmcl
    syl2anc
    recnd
    @6
    @13
    @6
    @26
    cB
    cX
    wcel
    @13
    cr
    wcel
    @27
    @6
    cU
    cX
    cB
    cX
    cR
    cU
    nmdvr.x
    nmdvr.u
    unitss
    @23
    sseldi
    cB
    cR
    cN
    cX
    nmdvr.x
    nmdvr.n
    nmcl
    syl2anc
    recnd
    @2
    @4
    @13
    cc0
    wne
    #
    @3
    @0
    @1
    @4
    @28
    cB
    cR
    cU
    cN
    nmdvr.n
    nmdvr.u
    unitnmn0
    3expa
    adantrl
    divrecd
    3eqtr4d
end
