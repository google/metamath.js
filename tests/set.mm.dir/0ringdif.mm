include "crg.mm"
include "cnzr.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "csn.mm"
include "wceq.mm"
include "eldif.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cbs.mm"
include "a1i.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "0ring.mm"
include "ex.mm"
include "fveq2.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "impbid1.mm"
include "0ringnnzr.mm"
include "3bitr3rd.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem 0ringdif
  let cB: class B
  let cR: class R
  let c.0: class .0.
  let vk: setvar k
  let vx: setvar x
  assume 0ringdif.b: |- B = ( Base ` R )
  assume 0ringdif.0: |- .0. = ( 0g ` R )


  assert |- ( R e. ( Ring \ NzRing ) <-> ( R e. Ring /\ B = { .0. } ) )

  proof
    cR
    crg
    cnzr
    cdif
    wcel
    cR
    crg
    wcel
    #
    cR
    cnzr
    wcel
    wn
    #
    wa
    @0
    cB
    c.0
    csn
    #
    wceq
    #
    wa
    cR
    crg
    cnzr
    eldif
    @0
    @1
    @3
    @0
    cB
    chash
    cfv
    #
    c1
    wceq
    #
    cR
    cbs
    cfv
    #
    chash
    cfv
    #
    c1
    wceq
    @3
    @1
    @0
    @4
    @7
    c1
    @0
    cB
    @6
    chash
    cB
    @6
    wceq
    @0
    0ringdif.b
    a1i
    fveq2d
    eqeq1d
    @0
    @5
    @3
    @0
    @5
    @3
    cB
    cR
    c.0
    0ringdif.b
    0ringdif.0
    0ring
    ex
    @3
    @4
    @2
    chash
    cfv
    #
    c1
    cB
    @2
    chash
    fveq2
    c.0
    cvv
    wcel
    @8
    c1
    wceq
    c.0
    cR
    c0g
    cfv
    cvv
    0ringdif.0
    cR
    c0g
    fvex
    eqeltri
    c.0
    cvv
    hashsng
    ax-mp
    syl6eq
    impbid1
    cR
    0ringnnzr
    3bitr3rd
    pm5.32i
    bitri
end
