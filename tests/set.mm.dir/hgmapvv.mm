include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "wne.mm"
include "wa.mm"
include "chdma.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cur.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "cinvr.mm"
include "coch.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "hgmapvvlem3.mm"
include "hgmapval0.mm"
include "eqtrd.mm"
include "pm2.61ne.mm"

theorem hgmapvv
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  assume hgmapvv.h: |- H = ( LHyp ` K )
  assume hgmapvv.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapvv.r: |- R = ( Scalar ` U )
  assume hgmapvv.b: |- B = ( Base ` R )
  assume hgmapvv.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapvv.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmapvv.j: |- ( ph -> X e. B )


  assert |- ( ph -> ( G ` ( G ` X ) ) = X )

  proof
    wph
    cX
    cG
    cfv
    #
    cG
    cfv
    #
    cX
    wceq
    cR
    c0g
    cfv
    #
    cG
    cfv
    #
    cG
    cfv
    #
    @2
    wceq
    cX
    @2
    cX
    @2
    wceq
    #
    @1
    @4
    cX
    @2
    @5
    @0
    @3
    cG
    cX
    @2
    cG
    fveq2
    fveq2d
    @5
    id
    eqeq12d
    wph
    cX
    @2
    wne
    #
    wa
    #
    cB
    cR
    cW
    cK
    chdma
    cfv
    cfv
    #
    cU
    cvsca
    cfv
    #
    cR
    cmulr
    cfv
    #
    cU
    cR
    cur
    cfv
    #
    cid
    cK
    cbs
    cfv
    cres
    cid
    cW
    cK
    cltrn
    cfv
    cfv
    cres
    cop
    #
    cG
    cH
    cK
    cR
    cinvr
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cU
    cbs
    cfv
    #
    cW
    cX
    @2
    hgmapvv.h
    @12
    eqid
    @14
    eqid
    hgmapvv.u
    @15
    eqid
    @9
    eqid
    hgmapvv.r
    hgmapvv.b
    @10
    eqid
    @2
    eqid
    #
    @11
    eqid
    @13
    eqid
    @8
    eqid
    hgmapvv.g
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @6
    hgmapvv.k
    adantr
    @7
    cX
    cB
    wcel
    #
    @6
    wa
    cX
    cB
    @2
    csn
    cdif
    wcel
    wph
    @17
    @6
    hgmapvv.j
    anim1i
    cX
    cB
    @2
    eldifsn
    sylibr
    hgmapvvlem3
    wph
    @4
    @3
    @2
    wph
    @3
    @2
    cG
    wph
    cR
    cU
    cG
    cH
    cK
    cW
    @2
    hgmapvv.h
    hgmapvv.u
    hgmapvv.r
    @16
    hgmapvv.g
    hgmapvv.k
    hgmapval0
    #
    fveq2d
    @18
    eqtrd
    pm2.61ne
end
