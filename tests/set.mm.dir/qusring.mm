include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "wceq.mm"
include "eqid.mm"
include "qus1.mm"
include "simpld.mm"

theorem qusring
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let c.1: class .1.
  let cX: class X
  assume qusring.u: |- U = ( R /s ( R ~QG S ) )
  assume qusring.i: |- I = ( 2Ideal ` R )


  assert |- ( ( R e. Ring /\ S e. I ) -> U e. Ring )

  proof
    cR
    crg
    wcel
    cS
    cI
    wcel
    wa
    cU
    crg
    wcel
    cR
    cur
    cfv
    #
    cR
    cS
    cqg
    co
    cec
    cU
    cur
    cfv
    wceq
    cR
    cS
    cU
    @0
    cI
    qusring.u
    qusring.i
    @0
    eqid
    qus1
    simpld
end
