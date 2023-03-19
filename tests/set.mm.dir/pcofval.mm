include "ctop.mm"
include "wcel.mm"
include "cpco.mm"
include "cfv.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "df-pco.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "dmmptss.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"
include "cntop2.mm"
include "eq0rdv.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "mpt20.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem pcofval
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let cJ: class J
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cK: class K
  let wph: wff ph
  let cX: class X
  let cH: class H
  let vj: setvar j

  disjoint f g
  disjoint f x
  disjoint g x
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint K x
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint H x
  disjoint H y
  disjoint f j
  disjoint g j
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint J y
  disjoint J z
  assert |- ( *p ` J ) = ( f e. ( II Cn J ) , g e. ( II Cn J ) |-> ( x e. ( 0 [,] 1 ) |-> if ( x <_ ( 1 / 2 ) , ( f ` ( 2 x. x ) ) , ( g ` ( ( 2 x. x ) - 1 ) ) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    cpco
    cfv
    #
    vf
    vg
    cii
    cJ
    ccn
    co
    #
    @2
    vx
    cc0
    c1
    cicc
    co
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    cle
    wbr
    c2
    @3
    cmul
    co
    #
    vf
    cv
    #
    cfv
    @4
    c1
    cmin
    co
    vg
    cv
    cfv
    cif
    cmpt
    #
    cmpt2
    #
    wceq
    vj
    cJ
    vf
    vg
    cii
    vj
    cv
    #
    ccn
    co
    #
    @9
    @6
    cmpt2
    #
    @7
    ctop
    cpco
    @8
    cJ
    wceq
    #
    vf
    vg
    @9
    @9
    @6
    @2
    @2
    @6
    @8
    cJ
    cii
    ccn
    oveq2
    #
    @12
    @11
    @6
    eqidd
    mpt2eq123dv
    vx
    vf
    vg
    vj
    df-pco
    #
    vf
    vg
    @2
    @2
    @6
    cii
    cJ
    ccn
    ovex
    #
    @14
    mpt2ex
    fvmpt
    @0
    wn
    #
    @1
    c0
    @7
    @15
    cJ
    cpco
    cdm
    #
    wcel
    #
    wn
    @1
    c0
    wceq
    @17
    @0
    @16
    ctop
    cJ
    vj
    ctop
    @10
    cpco
    @13
    dmmptss
    sseli
    con3i
    cJ
    cpco
    ndmfv
    syl
    @15
    @7
    vf
    vg
    c0
    c0
    @6
    cmpt2
    #
    c0
    @15
    @2
    c0
    wceq
    #
    @19
    @7
    @18
    wceq
    @15
    vf
    @2
    @5
    @2
    wcel
    @0
    @5
    cii
    cJ
    cntop2
    con3i
    eq0rdv
    #
    @20
    vf
    vg
    @2
    @2
    c0
    c0
    @6
    mpt2eq12
    syl2anc
    vf
    vg
    c0
    @6
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
end
