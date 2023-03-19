include "cfv.mm"
include "wceq.mm"
include "cur.mm"
include "cif.mm"
include "wcel.mm"
include "eqid.mm"
include "uvcvval.mm"
include "syl31anc.mm"
include "wne.mm"
include "wn.mm"
include "nesym.mm"
include "sylib.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem uvcvv0
  let wph: wff ph
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume uvcvv.u: |- U = ( R unitVec I )
  assume uvcvv.r: |- ( ph -> R e. V )
  assume uvcvv.i: |- ( ph -> I e. W )
  assume uvcvv.j: |- ( ph -> J e. I )
  assume uvcvv0.k: |- ( ph -> K e. I )
  assume uvcvv0.jk: |- ( ph -> J =/= K )
  assume uvcvv0.z: |- .0. = ( 0g ` R )


  assert |- ( ph -> ( ( U ` J ) ` K ) = .0. )

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
    c.0
    cif
    #
    c.0
    wph
    cR
    cV
    wcel
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
    @3
    wceq
    uvcvv.r
    uvcvv.i
    uvcvv.j
    uvcvv0.k
    cR
    cU
    @2
    cI
    cJ
    cK
    cV
    cW
    c.0
    uvcvv.u
    @2
    eqid
    uvcvv0.z
    uvcvval
    syl31anc
    wph
    @1
    @2
    c.0
    wph
    cJ
    cK
    wne
    @1
    wn
    uvcvv0.jk
    cJ
    cK
    nesym
    sylib
    iffalsed
    eqtrd
end
