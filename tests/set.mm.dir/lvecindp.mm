include "wceq.mm"
include "co.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "csubg.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspsnsubg.mm"
include "syl2anc.mm"
include "wss.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lspdisj.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "lspsneli.mm"
include "subgdisj1.mm"
include "cdif.mm"
include "wne.mm"
include "lssneln0.mm"
include "eldifsni.mm"
include "lvecvscan2.mm"
include "mpbid.mm"
include "subgdisj2.mm"
include "jca.mm"

theorem lvecindp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lvecindp.v: |- V = ( Base ` W )
  assume lvecindp.p: |- .+ = ( +g ` W )
  assume lvecindp.f: |- F = ( Scalar ` W )
  assume lvecindp.k: |- K = ( Base ` F )
  assume lvecindp.t: |- .x. = ( .s ` W )
  assume lvecindp.s: |- S = ( LSubSp ` W )
  assume lvecindp.w: |- ( ph -> W e. LVec )
  assume lvecindp.u: |- ( ph -> U e. S )
  assume lvecindp.x: |- ( ph -> X e. V )
  assume lvecindp.n: |- ( ph -> -. X e. U )
  assume lvecindp.y: |- ( ph -> Y e. U )
  assume lvecindp.z: |- ( ph -> Z e. U )
  assume lvecindp.a: |- ( ph -> A e. K )
  assume lvecindp.b: |- ( ph -> B e. K )
  assume lvecindp.e: |- ( ph -> ( ( A .x. X ) .+ Y ) = ( ( B .x. X ) .+ Z ) )


  assert |- ( ph -> ( A = B /\ Y = Z ) )

  proof
    wph
    cA
    cB
    wceq
    #
    cY
    cZ
    wceq
    wph
    cA
    cX
    c.x
    co
    #
    cB
    cX
    c.x
    co
    #
    wceq
    @0
    wph
    @1
    cY
    @2
    cZ
    c.pl
    cX
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    cU
    cW
    cW
    c0g
    cfv
    #
    cW
    ccntz
    cfv
    #
    lvecindp.p
    @5
    eqid
    #
    @6
    eqid
    #
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    @4
    cW
    csubg
    cfv
    #
    wcel
    wph
    cW
    clvec
    wcel
    @9
    lvecindp.w
    cW
    lveclmod
    syl
    #
    lvecindp.x
    @3
    cV
    cW
    cX
    lvecindp.v
    @3
    eqid
    #
    lspsnsubg
    syl2anc
    #
    wph
    cS
    @10
    cU
    wph
    @9
    cS
    @10
    wss
    @11
    cS
    cW
    lvecindp.s
    lsssssubg
    syl
    lvecindp.u
    sseldd
    #
    wph
    cS
    cU
    @3
    cV
    cW
    cX
    @5
    lvecindp.v
    @7
    @12
    lvecindp.s
    lvecindp.w
    lvecindp.u
    lvecindp.x
    lvecindp.n
    lspdisj
    #
    wph
    @4
    cU
    cW
    @6
    @8
    wph
    @9
    cW
    cabl
    wcel
    @11
    cW
    lmodabl
    syl
    @13
    @14
    ablcntzd
    #
    wph
    cA
    c.x
    cF
    cK
    @3
    cV
    cW
    cX
    lvecindp.v
    lvecindp.t
    lvecindp.f
    lvecindp.k
    @12
    @11
    lvecindp.a
    lvecindp.x
    lspsneli
    #
    wph
    cB
    c.x
    cF
    cK
    @3
    cV
    cW
    cX
    lvecindp.v
    lvecindp.t
    lvecindp.f
    lvecindp.k
    @12
    @11
    lvecindp.b
    lvecindp.x
    lspsneli
    #
    lvecindp.y
    lvecindp.z
    lvecindp.e
    subgdisj1
    wph
    cA
    cB
    c.x
    cF
    cK
    cV
    cW
    cX
    @5
    lvecindp.v
    lvecindp.t
    lvecindp.f
    lvecindp.k
    @7
    lvecindp.w
    lvecindp.a
    lvecindp.b
    lvecindp.x
    wph
    cX
    cV
    @5
    csn
    cdif
    wcel
    cX
    @5
    wne
    wph
    cS
    cU
    cV
    cW
    cX
    @5
    lvecindp.v
    @7
    lvecindp.s
    @11
    lvecindp.u
    lvecindp.x
    lvecindp.n
    lssneln0
    cX
    cV
    @5
    eldifsni
    syl
    lvecvscan2
    mpbid
    wph
    @1
    cY
    @2
    cZ
    c.pl
    @4
    cU
    cW
    @5
    @6
    lvecindp.p
    @7
    @8
    @13
    @14
    @15
    @16
    @17
    @18
    lvecindp.y
    lvecindp.z
    lvecindp.e
    subgdisj2
    jca
end
