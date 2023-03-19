include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cpco.mm"
include "cfv.mm"
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
include "wceq.mm"
include "wa.mm"
include "fveq1.mm"
include "adantr.mm"
include "adantl.mm"
include "ifeq12d.mm"
include "mpteq2dv.mm"
include "pcofval.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"

theorem pcoval
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cG: class G
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cX: class X
  let cH: class H
  let vj: setvar j
  assume pcoval.2: |- ( ph -> F e. ( II Cn J ) )
  assume pcoval.3: |- ( ph -> G e. ( II Cn J ) )

  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint J x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G g
  disjoint G y
  disjoint G z
  disjoint K x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint H x
  disjoint H y
  disjoint f j
  disjoint J f
  disjoint g j
  disjoint J g
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint J y
  disjoint J z
  assert |- ( ph -> ( F ( *p ` J ) G ) = ( x e. ( 0 [,] 1 ) |-> if ( x <_ ( 1 / 2 ) , ( F ` ( 2 x. x ) ) , ( G ` ( ( 2 x. x ) - 1 ) ) ) ) )

  proof
    wph
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    cG
    @0
    wcel
    cF
    cG
    cJ
    cpco
    cfv
    #
    co
    vx
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    cle
    wbr
    #
    c2
    @3
    cmul
    co
    #
    cF
    cfv
    #
    @5
    c1
    cmin
    co
    #
    cG
    cfv
    #
    cif
    #
    cmpt
    #
    wceq
    pcoval.2
    pcoval.3
    vf
    vg
    cF
    cG
    @0
    @0
    vx
    @2
    @4
    @5
    vf
    cv
    #
    cfv
    #
    @7
    vg
    cv
    #
    cfv
    #
    cif
    #
    cmpt
    @10
    @1
    @11
    cF
    wceq
    #
    @13
    cG
    wceq
    #
    wa
    #
    vx
    @2
    @15
    @9
    @18
    @4
    @12
    @6
    @14
    @8
    @16
    @12
    @6
    wceq
    @17
    @5
    @11
    cF
    fveq1
    adantr
    @17
    @14
    @8
    wceq
    @16
    @7
    @13
    cG
    fveq1
    adantl
    ifeq12d
    mpteq2dv
    vx
    vf
    vg
    cJ
    pcofval
    vx
    @2
    @9
    cc0
    c1
    cicc
    ovex
    mptex
    ovmpt2a
    syl2anc
end
