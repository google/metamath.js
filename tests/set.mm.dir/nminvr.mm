include "cnrg.mm"
include "wcel.mm"
include "cnzr.mm"
include "w3a.mm"
include "cfv.mm"
include "c1.mm"
include "cngp.mm"
include "cbs.mm"
include "cr.mm"
include "nrgngp.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "unitcl.mm"
include "3ad2ant3.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "recnd.mm"
include "crg.mm"
include "nzrring.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "ringinvcl.mm"
include "unitnmn0.mm"
include "cmulr.mm"
include "co.mm"
include "cur.mm"
include "cmul.mm"
include "wceq.mm"
include "unitrinv.mm"
include "fveq2d.mm"
include "simp1.mm"
include "nmmul.mm"
include "syl3anc.mm"
include "nm1.mm"
include "3adant3.mm"
include "3eqtr3d.mm"
include "mvllmuld.mm"

theorem nminvr
  let cA: class A
  let cR: class R
  let cU: class U
  let cI: class I
  let cN: class N
  assume nminvr.n: |- N = ( norm ` R )
  assume nminvr.u: |- U = ( Unit ` R )
  assume nminvr.i: |- I = ( invr ` R )


  assert |- ( ( R e. NrmRing /\ R e. NzRing /\ A e. U ) -> ( N ` ( I ` A ) ) = ( 1 / ( N ` A ) ) )

  proof
    cR
    cnrg
    wcel
    #
    cR
    cnzr
    wcel
    #
    cA
    cU
    wcel
    #
    w3a
    #
    cA
    cN
    cfv
    #
    cA
    cI
    cfv
    #
    cN
    cfv
    #
    c1
    @3
    @4
    @3
    cR
    cngp
    wcel
    #
    cA
    cR
    cbs
    cfv
    #
    wcel
    #
    @4
    cr
    wcel
    @0
    @1
    @7
    @2
    cR
    nrgngp
    3ad2ant1
    #
    @2
    @0
    @9
    @1
    @8
    cR
    cU
    cA
    @8
    eqid
    #
    nminvr.u
    unitcl
    3ad2ant3
    #
    cA
    cR
    cN
    @8
    @11
    nminvr.n
    nmcl
    syl2anc
    recnd
    @3
    @6
    @3
    @7
    @5
    @8
    wcel
    #
    @6
    cr
    wcel
    @10
    @3
    cR
    crg
    wcel
    #
    @2
    @13
    @1
    @0
    @14
    @2
    cR
    nzrring
    3ad2ant2
    #
    @0
    @1
    @2
    simp3
    #
    @8
    cR
    cU
    cI
    cA
    nminvr.u
    nminvr.i
    @11
    ringinvcl
    syl2anc
    #
    @5
    cR
    cN
    @8
    @11
    nminvr.n
    nmcl
    syl2anc
    recnd
    cA
    cR
    cU
    cN
    nminvr.n
    nminvr.u
    unitnmn0
    @3
    cA
    @5
    cR
    cmulr
    cfv
    #
    co
    #
    cN
    cfv
    #
    cR
    cur
    cfv
    #
    cN
    cfv
    #
    @4
    @6
    cmul
    co
    #
    c1
    @3
    @19
    @21
    cN
    @3
    @14
    @2
    @19
    @21
    wceq
    @15
    @16
    cR
    @18
    cU
    @21
    cI
    cA
    nminvr.u
    nminvr.i
    @18
    eqid
    #
    @21
    eqid
    #
    unitrinv
    syl2anc
    fveq2d
    @3
    @0
    @9
    @13
    @20
    @23
    wceq
    @0
    @1
    @2
    simp1
    @12
    @17
    cA
    @5
    cR
    @18
    cN
    @8
    @11
    nminvr.n
    @24
    nmmul
    syl3anc
    @0
    @1
    @22
    c1
    wceq
    @2
    cR
    @21
    cN
    nminvr.n
    @25
    nm1
    3adant3
    3eqtr3d
    mvllmuld
end
