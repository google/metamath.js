include "crg.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "wne.mm"
include "cnzr.mm"
include "simpl.mm"
include "eldifsni.mm"
include "adantl.mm"
include "wceq.mm"
include "wi.mm"
include "eldifi.mm"
include "ring0cl.mm"
include "adantr.mm"
include "eqid.mm"
include "ring1eq0.mm"
include "syl3anc.mm"
include "necon3d.mm"
include "mpd.mm"
include "isnzr.mm"
include "sylanbrc.mm"

theorem ringelnzr
  let cB: class B
  let cR: class R
  let cX: class X
  let c.0: class .0.
  assume ringelnzr.z: |- .0. = ( 0g ` R )
  assume ringelnzr.b: |- B = ( Base ` R )


  assert |- ( ( R e. Ring /\ X e. ( B \ { .0. } ) ) -> R e. NzRing )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    c.0
    csn
    #
    cdif
    wcel
    #
    wa
    #
    @0
    cR
    cur
    cfv
    #
    c.0
    wne
    #
    cR
    cnzr
    wcel
    @0
    @2
    simpl
    #
    @3
    cX
    c.0
    wne
    #
    @5
    @2
    @7
    @0
    cX
    cB
    c.0
    eldifsni
    adantl
    @3
    @4
    c.0
    cX
    c.0
    @3
    @0
    cX
    cB
    wcel
    #
    c.0
    cB
    wcel
    #
    @4
    c.0
    wceq
    cX
    c.0
    wceq
    wi
    @6
    @2
    @8
    @0
    cX
    cB
    @1
    eldifi
    adantl
    @0
    @9
    @2
    cB
    cR
    c.0
    ringelnzr.b
    ringelnzr.z
    ring0cl
    adantr
    cB
    cR
    @4
    cX
    c.0
    c.0
    ringelnzr.b
    @4
    eqid
    #
    ringelnzr.z
    ring1eq0
    syl3anc
    necon3d
    mpd
    cR
    @4
    c.0
    @10
    ringelnzr.z
    isnzr
    sylanbrc
end
