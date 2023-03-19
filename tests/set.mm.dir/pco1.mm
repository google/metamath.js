include "c1.mm"
include "cpco.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
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
include "pcoval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "1elunit.mm"
include "clt.mm"
include "wn.mm"
include "halflt1.mm"
include "halfre.mm"
include "1re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "breq1.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "oveq2.mm"
include "2t1e2.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "2m1e1.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ax-mp.mm"

theorem pco1
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cX: class X
  let cH: class H
  let vj: setvar j
  assume pcoval.2: |- ( ph -> F e. ( II Cn J ) )
  assume pcoval.3: |- ( ph -> G e. ( II Cn J ) )


  assert |- ( ph -> ( ( F ( *p ` J ) G ) ` 1 ) = ( G ` 1 ) )

  proof
    wph
    c1
    cF
    cG
    cJ
    cpco
    cfv
    co
    #
    cfv
    c1
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
    #
    cle
    wbr
    #
    c2
    @2
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
    cfv
    #
    c1
    cG
    cfv
    #
    wph
    c1
    @0
    @10
    wph
    vx
    cF
    cG
    cJ
    pcoval.2
    pcoval.3
    pcoval
    fveq1d
    c1
    @1
    wcel
    @11
    @12
    wceq
    1elunit
    vx
    c1
    @9
    @12
    @1
    @10
    @2
    c1
    wceq
    #
    @9
    @8
    @12
    @13
    @4
    @6
    @8
    @13
    @4
    c1
    @3
    cle
    wbr
    #
    @3
    c1
    clt
    wbr
    @14
    wn
    halflt1
    @3
    c1
    halfre
    1re
    ltnlei
    mpbi
    @2
    c1
    @3
    cle
    breq1
    mtbiri
    iffalsed
    @13
    @7
    c1
    cG
    @13
    @7
    c2
    c1
    cmin
    co
    c1
    @13
    @5
    c2
    c1
    cmin
    @13
    @5
    c2
    c1
    cmul
    co
    c2
    @2
    c1
    c2
    cmul
    oveq2
    2t1e2
    syl6eq
    oveq1d
    2m1e1
    syl6eq
    fveq2d
    eqtrd
    @10
    eqid
    c1
    cG
    fvex
    fvmpt
    ax-mp
    syl6eq
end
