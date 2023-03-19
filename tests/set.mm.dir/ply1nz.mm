include "cnzr.mm"
include "wcel.mm"
include "crg.mm"
include "cur.mm"
include "cfv.mm"
include "cascl.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "nzrring.mm"
include "ply1ring.mm"
include "syl.mm"
include "wne.mm"
include "wf.mm"
include "eqid.mm"
include "ply1sclf.mm"
include "ringidcl.mm"
include "ffvelrnd.mm"
include "nzrnz.mm"
include "ply1scln0.mm"
include "syl3anc.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ringelnzr.mm"
include "syl2anc.mm"

theorem ply1nz
  let cP: class P
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume ply1domn.p: |- P = ( Poly1 ` R )


  assert |- ( R e. NzRing -> P e. NzRing )

  proof
    cR
    cnzr
    wcel
    #
    cP
    crg
    wcel
    #
    cR
    cur
    cfv
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cP
    cbs
    cfv
    #
    cP
    c0g
    cfv
    #
    csn
    cdif
    wcel
    #
    cP
    cnzr
    wcel
    @0
    cR
    crg
    wcel
    #
    @1
    cR
    nzrring
    #
    cP
    cR
    ply1domn.p
    ply1ring
    syl
    @0
    @4
    @5
    wcel
    @4
    @6
    wne
    #
    @7
    @0
    cR
    cbs
    cfv
    #
    @5
    @2
    @3
    @0
    @8
    @11
    @5
    @3
    wf
    @9
    @3
    @5
    cP
    cR
    @11
    ply1domn.p
    @3
    eqid
    #
    @11
    eqid
    #
    @5
    eqid
    #
    ply1sclf
    syl
    @0
    @8
    @2
    @11
    wcel
    #
    @9
    @11
    cR
    @2
    @13
    @2
    eqid
    #
    ringidcl
    syl
    #
    ffvelrnd
    @0
    @8
    @15
    @2
    cR
    c0g
    cfv
    #
    wne
    @10
    @9
    @17
    cR
    @2
    @18
    @16
    @18
    eqid
    #
    nzrnz
    @3
    cP
    cR
    @11
    @2
    @6
    @18
    ply1domn.p
    @12
    @19
    @6
    eqid
    #
    @13
    ply1scln0
    syl3anc
    @4
    @5
    @6
    eldifsn
    sylanbrc
    @5
    cP
    @4
    @6
    @20
    @14
    ringelnzr
    syl2anc
end
