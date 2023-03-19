include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cicc.mm"
include "wcel.mm"
include "wa.mm"
include "cpco.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "cc0.mm"
include "wceq.mm"
include "cr.mm"
include "wss.mm"
include "0re.mm"
include "1re.mm"
include "halfre.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "1le1.mm"
include "iccss.mm"
include "mp4an.mm"
include "sseli.mm"
include "pcovalg.mm"
include "sylan2.mm"
include "adantr.mm"
include "simprr.mm"
include "elicc2i.mm"
include "simp2bi.mm"
include "ad2antrl.mm"
include "wb.mm"
include "simp1bi.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "oveq2d.mm"
include "2cn.mm"
include "2ne0.mm"
include "recidi.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "1m1e0.mm"
include "3eqtr4d.mm"
include "ifeq1d.mm"
include "ifid.mm"
include "expr.mm"
include "iffalse.mm"
include "pm2.61d1.mm"
include "eqtrd.mm"

theorem pcoval2
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cH: class H
  let vj: setvar j
  assume pcoval.2: |- ( ph -> F e. ( II Cn J ) )
  assume pcoval.3: |- ( ph -> G e. ( II Cn J ) )
  assume pcoval2.4: |- ( ph -> ( F ` 1 ) = ( G ` 0 ) )


  assert |- ( ( ph /\ X e. ( ( 1 / 2 ) [,] 1 ) ) -> ( ( F ( *p ` J ) G ) ` X ) = ( G ` ( ( 2 x. X ) - 1 ) ) )

  proof
    wph
    cX
    c1
    c2
    cdiv
    co
    #
    c1
    cicc
    co
    #
    wcel
    #
    wa
    #
    cX
    cF
    cG
    cJ
    cpco
    cfv
    co
    cfv
    #
    cX
    @0
    cle
    wbr
    #
    c2
    cX
    cmul
    co
    #
    cF
    cfv
    #
    @6
    c1
    cmin
    co
    #
    cG
    cfv
    #
    cif
    #
    @9
    @2
    wph
    cX
    cc0
    c1
    cicc
    co
    #
    wcel
    @4
    @10
    wceq
    @1
    @11
    cX
    cc0
    cr
    wcel
    c1
    cr
    wcel
    cc0
    @0
    cle
    wbr
    c1
    c1
    cle
    wbr
    @1
    @11
    wss
    0re
    1re
    cc0
    @0
    0re
    halfre
    halfgt0
    ltleii
    1le1
    cc0
    c1
    @0
    c1
    iccss
    mp4an
    sseli
    wph
    cF
    cG
    cJ
    cX
    pcoval.2
    pcoval.3
    pcovalg
    sylan2
    @3
    @5
    @10
    @9
    wceq
    #
    wph
    @2
    @5
    @12
    wph
    @2
    @5
    wa
    #
    wa
    #
    @10
    @5
    @9
    @9
    cif
    @9
    @14
    @5
    @7
    @9
    @9
    @14
    c1
    cF
    cfv
    #
    cc0
    cG
    cfv
    #
    @7
    @9
    wph
    @15
    @16
    wceq
    @13
    pcoval2.4
    adantr
    @14
    @6
    c1
    cF
    @14
    @6
    c2
    @0
    cmul
    co
    c1
    @14
    cX
    @0
    c2
    cmul
    @14
    cX
    @0
    wceq
    #
    @5
    @0
    cX
    cle
    wbr
    #
    wph
    @2
    @5
    simprr
    @2
    @18
    wph
    @5
    @2
    cX
    cr
    wcel
    #
    @18
    cX
    c1
    cle
    wbr
    #
    @0
    c1
    cX
    halfre
    1re
    elicc2i
    #
    simp2bi
    ad2antrl
    @14
    @19
    @0
    cr
    wcel
    @17
    @5
    @18
    wa
    wb
    @2
    @19
    wph
    @5
    @2
    @19
    @18
    @20
    @21
    simp1bi
    ad2antrl
    halfre
    cX
    @0
    letri3
    sylancl
    mpbir2and
    oveq2d
    c2
    2cn
    2ne0
    recidi
    syl6eq
    #
    fveq2d
    @14
    @8
    cc0
    cG
    @14
    @8
    c1
    c1
    cmin
    co
    cc0
    @14
    @6
    c1
    c1
    cmin
    @22
    oveq1d
    1m1e0
    syl6eq
    fveq2d
    3eqtr4d
    ifeq1d
    @5
    @9
    ifid
    syl6eq
    expr
    @5
    @7
    @9
    iffalse
    pm2.61d1
    eqtrd
end
