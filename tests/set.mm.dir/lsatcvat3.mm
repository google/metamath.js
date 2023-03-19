include "clcv.mm"
include "cfv.mm"
include "co.mm"
include "cin.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lssincl.mm"
include "wss.mm"
include "wn.mm"
include "wbr.mm"
include "lcv1.mm"
include "mpbid.mm"
include "cabl.mm"
include "csubg.mm"
include "wceq.mm"
include "lmodabl.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lsmcom.mm"
include "oveq2d.mm"
include "lsmass.mm"
include "eqtr4d.mm"
include "lsmless2.mm"
include "eqsstrd.mm"
include "lsmidm.mm"
include "sseqtrd.mm"
include "lsmub2.mm"
include "syl2anc.mm"
include "eqssd.mm"
include "breqtrrd.mm"
include "lcvexchlem4.mm"
include "lsatcvat2.mm"

theorem lsatcvat3
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cW: class W
  assume lsatcvat3.s: |- S = ( LSubSp ` W )
  assume lsatcvat3.p: |- .(+) = ( LSSum ` W )
  assume lsatcvat3.a: |- A = ( LSAtoms ` W )
  assume lsatcvat3.w: |- ( ph -> W e. LVec )
  assume lsatcvat3.u: |- ( ph -> U e. S )
  assume lsatcvat3.q: |- ( ph -> Q e. A )
  assume lsatcvat3.r: |- ( ph -> R e. A )
  assume lsatcvat3.n: |- ( ph -> Q =/= R )
  assume lsatcvat3.m: |- ( ph -> -. R C_ U )
  assume lsatcvat3.l: |- ( ph -> Q C_ ( U .(+) R ) )


  assert |- ( ph -> ( U i^i ( Q .(+) R ) ) e. A )

  proof
    wph
    cA
    cW
    clcv
    cfv
    #
    c.po
    cQ
    cR
    cS
    cU
    cQ
    cR
    c.po
    co
    #
    cin
    #
    cW
    lsatcvat3.s
    lsatcvat3.p
    lsatcvat3.a
    @0
    eqid
    #
    lsatcvat3.w
    wph
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    @1
    cS
    wcel
    #
    @2
    cS
    wcel
    wph
    cW
    clvec
    wcel
    @4
    lsatcvat3.w
    cW
    lveclmod
    syl
    #
    lsatcvat3.u
    wph
    @4
    cQ
    cS
    wcel
    cR
    cS
    wcel
    #
    @6
    @7
    wph
    cA
    cS
    cQ
    cW
    lsatcvat3.s
    lsatcvat3.a
    @7
    lsatcvat3.q
    lsatlssel
    #
    wph
    cA
    cS
    cR
    cW
    lsatcvat3.s
    lsatcvat3.a
    @7
    lsatcvat3.r
    lsatlssel
    #
    c.po
    cS
    cQ
    cR
    cW
    lsatcvat3.s
    lsatcvat3.p
    lsmcl
    syl3anc
    #
    cS
    cU
    @1
    cW
    lsatcvat3.s
    lssincl
    syl3anc
    lsatcvat3.q
    lsatcvat3.r
    lsatcvat3.n
    wph
    @0
    c.po
    cS
    cU
    @1
    cW
    lsatcvat3.s
    lsatcvat3.p
    @3
    @7
    lsatcvat3.u
    @11
    wph
    cU
    cU
    cR
    c.po
    co
    #
    cU
    @1
    c.po
    co
    #
    @0
    wph
    cR
    cU
    wss
    wn
    cU
    @12
    @0
    wbr
    lsatcvat3.m
    wph
    cA
    @0
    c.po
    cR
    cS
    cU
    cW
    lsatcvat3.s
    lsatcvat3.p
    lsatcvat3.a
    @3
    lsatcvat3.w
    lsatcvat3.u
    lsatcvat3.r
    lcv1
    mpbid
    wph
    @13
    @12
    wph
    @13
    @12
    @12
    c.po
    co
    #
    @12
    wph
    @13
    @12
    cQ
    c.po
    co
    #
    @14
    wph
    @13
    cU
    cR
    cQ
    c.po
    co
    #
    c.po
    co
    #
    @15
    wph
    @1
    @16
    cU
    c.po
    wph
    cW
    cabl
    wcel
    #
    cQ
    cW
    csubg
    cfv
    #
    wcel
    #
    cR
    @19
    wcel
    #
    @1
    @16
    wceq
    wph
    @4
    @18
    @7
    cW
    lmodabl
    syl
    wph
    cS
    @19
    cQ
    wph
    @4
    cS
    @19
    wss
    @7
    cS
    cW
    lsatcvat3.s
    lsssssubg
    syl
    #
    @9
    sseldd
    #
    wph
    cS
    @19
    cR
    @22
    @10
    sseldd
    #
    c.po
    cQ
    cR
    cW
    lsatcvat3.p
    lsmcom
    syl3anc
    oveq2d
    wph
    cU
    @19
    wcel
    #
    @21
    @20
    @15
    @17
    wceq
    wph
    cS
    @19
    cU
    @22
    lsatcvat3.u
    sseldd
    #
    @24
    @23
    c.po
    cU
    cR
    cQ
    cW
    lsatcvat3.p
    lsmass
    syl3anc
    eqtr4d
    wph
    @12
    @19
    wcel
    #
    @27
    cQ
    @12
    wss
    @15
    @14
    wss
    wph
    cS
    @19
    @12
    @22
    wph
    @4
    @5
    @8
    @12
    cS
    wcel
    @7
    lsatcvat3.u
    @10
    c.po
    cS
    cU
    cR
    cW
    lsatcvat3.s
    lsatcvat3.p
    lsmcl
    syl3anc
    sseldd
    #
    @28
    lsatcvat3.l
    c.po
    @12
    cQ
    @12
    cW
    lsatcvat3.p
    lsmless2
    syl3anc
    eqsstrd
    wph
    @27
    @14
    @12
    wceq
    @28
    c.po
    @12
    cW
    lsatcvat3.p
    lsmidm
    syl
    sseqtrd
    wph
    @25
    @1
    @19
    wcel
    cR
    @1
    wss
    #
    @12
    @13
    wss
    @26
    wph
    cS
    @19
    @1
    @22
    @11
    sseldd
    wph
    @20
    @21
    @29
    @23
    @24
    c.po
    cQ
    cR
    cW
    lsatcvat3.p
    lsmub2
    syl2anc
    c.po
    cU
    cR
    @1
    cW
    lsatcvat3.p
    lsmless2
    syl3anc
    eqssd
    breqtrrd
    lcvexchlem4
    lsatcvat2
end
