include "cprds.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "cdsmm.mm"
include "cbs.mm"
include "cfv.mm"
include "clss.mm"
include "eqid.mm"
include "prdslmodd.mm"
include "dsmmlss.mm"
include "cress.mm"
include "dsmmval2.mm"
include "eqtri.mm"
include "lsslmod.mm"
include "syl2anc.mm"

theorem dsmmlmod
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cR: class R
  let cS: class S
  let cI: class I
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cP: class P
  let cU: class U
  let cH: class H
  assume dsmmlss.i: |- ( ph -> I e. W )
  assume dsmmlss.s: |- ( ph -> S e. Ring )
  assume dsmmlss.r: |- ( ph -> R : I --> LMod )
  assume dsmmlss.k: |- ( ( ph /\ x e. I ) -> ( Scalar ` ( R ` x ) ) = S )
  assume dsmmlmod.c: |- C = ( S (+)m R )

  disjoint ph x
  disjoint S x
  disjoint R x
  disjoint I x
  disjoint a ph
  disjoint b ph
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint S a
  disjoint S b
  disjoint R a
  disjoint R b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint P x
  disjoint U a
  disjoint U b
  disjoint H a
  disjoint H b
  disjoint H x
  assert |- ( ph -> C e. LMod )

  proof
    wph
    cS
    cR
    cprds
    co
    #
    clmod
    wcel
    cS
    cR
    cdsmm
    co
    #
    cbs
    cfv
    #
    @0
    clss
    cfv
    #
    wcel
    cC
    clmod
    wcel
    wph
    vx
    cR
    cS
    cI
    cW
    @0
    @0
    eqid
    #
    dsmmlss.s
    dsmmlss.i
    dsmmlss.r
    dsmmlss.k
    prdslmodd
    wph
    vx
    @0
    cR
    cS
    @3
    @2
    cI
    cW
    dsmmlss.i
    dsmmlss.s
    dsmmlss.r
    dsmmlss.k
    @4
    @3
    eqid
    #
    @2
    eqid
    #
    dsmmlss
    @3
    @2
    @0
    cC
    cC
    @1
    @0
    @2
    cress
    co
    dsmmlmod.c
    @2
    cR
    cS
    @6
    dsmmval2
    eqtri
    @5
    lsslmod
    syl2anc
end
