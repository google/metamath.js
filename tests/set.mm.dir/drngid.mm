include "cdr.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cui.mm"
include "cress.mm"
include "co.mm"
include "c0g.mm"
include "crg.mm"
include "wceq.mm"
include "drngring.mm"
include "eqid.mm"
include "unitgrpid.mm"
include "syl.mm"
include "csn.mm"
include "cdif.mm"
include "isdrng.mm"
include "simprbi.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem drngid
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let cG: class G
  let c.0: class .0.
  assume drngid.b: |- B = ( Base ` R )
  assume drngid.z: |- .0. = ( 0g ` R )
  assume drngid.u: |- .1. = ( 1r ` R )
  assume drngid.g: |- G = ( ( mulGrp ` R ) |`s ( B \ { .0. } ) )


  assert |- ( R e. DivRing -> .1. = ( 0g ` G ) )

  proof
    cR
    cdr
    wcel
    #
    c.1
    cR
    cmgp
    cfv
    #
    cR
    cui
    cfv
    #
    cress
    co
    #
    c0g
    cfv
    #
    cG
    c0g
    cfv
    @0
    cR
    crg
    wcel
    #
    c.1
    @4
    wceq
    cR
    drngring
    cR
    @2
    c.1
    @3
    @2
    eqid
    #
    @3
    eqid
    drngid.u
    unitgrpid
    syl
    @0
    @3
    cG
    c0g
    @0
    @3
    @1
    cB
    c.0
    csn
    cdif
    #
    cress
    co
    cG
    @0
    @2
    @7
    @1
    cress
    @0
    @5
    @2
    @7
    wceq
    cB
    cR
    @2
    c.0
    drngid.b
    @6
    drngid.z
    isdrng
    simprbi
    oveq2d
    drngid.g
    syl6eqr
    fveq2d
    eqtrd
end
