include "cii.mm"
include "cxko.mm"
include "co.mm"
include "crest.mm"
include "cts.mm"
include "cfv.mm"
include "cbs.mm"
include "om1tset.mm"
include "oveq12d.mm"
include "ctopn.mm"
include "eqid.mm"
include "topnval.mm"
include "eqtr4i.mm"
include "syl6reqr.mm"

theorem om1opn
  let wph: wff ph
  let cB: class B
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let cF: class F
  let vf: setvar f
  assume om1bas.o: |- O = ( J Om1 Y )
  assume om1bas.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume om1bas.y: |- ( ph -> Y e. X )
  assume om1opn.k: |- K = ( TopOpen ` O )
  assume om1opn.b: |- ( ph -> B = ( Base ` O ) )


  assert |- ( ph -> K = ( ( J ^ko II ) |`t B ) )

  proof
    wph
    cJ
    cii
    cxko
    co
    #
    cB
    crest
    co
    cO
    cts
    cfv
    #
    cO
    cbs
    cfv
    #
    crest
    co
    #
    cK
    wph
    @0
    @1
    cB
    @2
    crest
    wph
    cJ
    cO
    cX
    cY
    om1bas.o
    om1bas.j
    om1bas.y
    om1tset
    om1opn.b
    oveq12d
    cK
    cO
    ctopn
    cfv
    @3
    om1opn.k
    @2
    @1
    cO
    @2
    eqid
    @1
    eqid
    topnval
    eqtr4i
    syl6reqr
end
