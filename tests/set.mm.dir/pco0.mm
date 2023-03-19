include "cc0.mm"
include "cpco.mm"
include "cfv.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "c1.mm"
include "cdiv.mm"
include "cicc.mm"
include "wcel.mm"
include "wceq.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "0re.mm"
include "0le0.mm"
include "halfre.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "elicc2i.mm"
include "mpbir3an.mm"
include "pcoval1.mm"
include "mpan2.mm"
include "2t0e0.mm"
include "fveq2i.mm"
include "syl6eq.mm"

theorem pco0
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


  assert |- ( ph -> ( ( F ( *p ` J ) G ) ` 0 ) = ( F ` 0 ) )

  proof
    wph
    cc0
    cF
    cG
    cJ
    cpco
    cfv
    co
    cfv
    #
    c2
    cc0
    cmul
    co
    #
    cF
    cfv
    #
    cc0
    cF
    cfv
    wph
    cc0
    cc0
    c1
    c2
    cdiv
    co
    #
    cicc
    co
    wcel
    #
    @0
    @2
    wceq
    @4
    cc0
    cr
    wcel
    cc0
    cc0
    cle
    wbr
    cc0
    @3
    cle
    wbr
    0re
    0le0
    cc0
    @3
    0re
    halfre
    halfgt0
    ltleii
    cc0
    @3
    cc0
    0re
    halfre
    elicc2i
    mpbir3an
    wph
    cF
    cG
    cJ
    cc0
    pcoval.2
    pcoval.3
    pcoval1
    mpan2
    @1
    cc0
    cF
    2t0e0
    fveq2i
    syl6eq
end
