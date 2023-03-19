include "c0.mm"
include "ctpos.mm"
include "wfn.mm"
include "wceq.mm"
include "ccnv.mm"
include "wrel.mm"
include "rel0.mm"
include "eqid.mm"
include "fn0.mm"
include "mpbir.mm"
include "tposfn2.mm"
include "mp2.mm"
include "cnv0.mm"
include "fneq2i.mm"
include "mpbi.mm"

theorem tpos0
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cF: class F
  let cG: class G


  assert |- tpos (/) = (/)

  proof
    c0
    ctpos
    #
    c0
    wfn
    #
    @0
    c0
    wceq
    @0
    c0
    ccnv
    #
    wfn
    #
    @1
    c0
    wrel
    c0
    c0
    wfn
    #
    @3
    rel0
    @4
    c0
    c0
    wceq
    c0
    eqid
    c0
    fn0
    mpbir
    c0
    c0
    tposfn2
    mp2
    @2
    c0
    @0
    cnv0
    fneq2i
    mpbi
    @0
    fn0
    mpbi
end
