include "cfv.mm"
include "wceq.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "crg.mm"
include "wcel.mm"
include "eqid.mm"
include "uvcvval.mm"
include "syl31anc.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem uvcvvcl2
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cK: class K
  let cW: class W
  assume uvcvvcl2.u: |- U = ( R unitVec I )
  assume uvcvvcl2.b: |- B = ( Base ` R )
  assume uvcvvcl2.r: |- ( ph -> R e. Ring )
  assume uvcvvcl2.i: |- ( ph -> I e. W )
  assume uvcvvcl2.j: |- ( ph -> J e. I )
  assume uvcvvcl2.k: |- ( ph -> K e. I )


  assert |- ( ph -> ( ( U ` J ) ` K ) e. B )

  proof
    wph
    cK
    cJ
    cU
    cfv
    cfv
    #
    cK
    cJ
    wceq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cB
    wph
    cR
    crg
    wcel
    #
    cI
    cW
    wcel
    cJ
    cI
    wcel
    cK
    cI
    wcel
    @0
    @4
    wceq
    uvcvvcl2.r
    uvcvvcl2.i
    uvcvvcl2.j
    uvcvvcl2.k
    cR
    cU
    @2
    cI
    cJ
    cK
    crg
    cW
    @3
    uvcvvcl2.u
    @2
    eqid
    #
    @3
    eqid
    #
    uvcvval
    syl31anc
    wph
    @5
    @4
    cB
    wcel
    uvcvvcl2.r
    @5
    @1
    @2
    @3
    cB
    cB
    cR
    @2
    uvcvvcl2.b
    @6
    ringidcl
    cB
    cR
    @3
    uvcvvcl2.b
    @7
    ring0cl
    ifcld
    syl
    eqeltrd
end
