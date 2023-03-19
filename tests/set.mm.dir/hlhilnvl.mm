include "cedring.mm"
include "cfv.mm"
include "cnx.mm"
include "cstv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "chg.mm"
include "eqeltri.mm"
include "starvid.mm"
include "setsid.mm"
include "mp2an.mm"
include "csca.mm"
include "eqid.mm"
include "hlhilsca.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "syl5eq.mm"

theorem hlhilnvl
  let wph: wff ph
  let cR: class R
  let cU: class U
  let cH: class H
  let c.as: class .*
  let cK: class K
  let cW: class W
  assume hlhilnvl.h: |- H = ( LHyp ` K )
  assume hlhilnvl.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilnvl.r: |- R = ( Scalar ` U )
  assume hlhilnvl.i: |- .* = ( ( HGMap ` K ) ` W )
  assume hlhilnvl.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> .* = ( *r ` R ) )

  proof
    wph
    c.as
    cW
    cK
    cedring
    cfv
    #
    cfv
    #
    cnx
    cstv
    cfv
    c.as
    cop
    csts
    co
    #
    cstv
    cfv
    #
    cR
    cstv
    cfv
    @1
    cvv
    wcel
    c.as
    cvv
    wcel
    c.as
    @3
    wceq
    cW
    @0
    fvex
    c.as
    cW
    cK
    chg
    cfv
    #
    cfv
    cvv
    hlhilnvl.i
    cW
    @4
    fvex
    eqeltri
    cvv
    c.as
    cstv
    cvv
    @1
    starvid
    setsid
    mp2an
    wph
    @2
    cR
    cstv
    wph
    @2
    cU
    csca
    cfv
    cR
    wph
    @2
    cU
    @1
    c.as
    cH
    cK
    cW
    hlhilnvl.h
    hlhilnvl.u
    hlhilnvl.k
    @1
    eqid
    hlhilnvl.i
    @2
    eqid
    hlhilsca
    hlhilnvl.r
    syl6eqr
    fveq2d
    syl5eq
end
