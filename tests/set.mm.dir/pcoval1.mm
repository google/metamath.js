include "cc0.mm"
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
include "wceq.mm"
include "cr.mm"
include "wss.mm"
include "0re.mm"
include "1re.mm"
include "0le0.mm"
include "halfre.mm"
include "halflt1.mm"
include "ltleii.mm"
include "iccss.mm"
include "mp4an.mm"
include "sseli.mm"
include "pcovalg.mm"
include "sylan2.mm"
include "elii1.mm"
include "simprbi.mm"
include "iftrued.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem pcoval1
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


  assert |- ( ( ph /\ X e. ( 0 [,] ( 1 / 2 ) ) ) -> ( ( F ( *p ` J ) G ) ` X ) = ( F ` ( 2 x. X ) ) )

  proof
    wph
    cX
    cc0
    c1
    c2
    cdiv
    co
    #
    cicc
    co
    #
    wcel
    #
    wa
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
    @5
    c1
    cmin
    co
    cG
    cfv
    #
    cif
    #
    @6
    @2
    wph
    cX
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    @3
    @8
    wceq
    @1
    @9
    cX
    cc0
    cr
    wcel
    c1
    cr
    wcel
    cc0
    cc0
    cle
    wbr
    @0
    c1
    cle
    wbr
    @1
    @9
    wss
    0re
    1re
    0le0
    @0
    c1
    halfre
    1re
    halflt1
    ltleii
    cc0
    c1
    cc0
    @0
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
    @2
    @8
    @6
    wceq
    wph
    @2
    @4
    @6
    @7
    @2
    @10
    @4
    cX
    elii1
    simprbi
    iftrued
    adantl
    eqtrd
end
