include "co.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lsatlssel.mm"
include "lsmub2.mm"
include "syl2anc.mm"
include "clcv.mm"
include "eqid.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "wpss.mm"
include "wbr.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "lcvp.mm"
include "mpbid.mm"
include "lcvpss.mm"
include "lsmub1.mm"
include "wa.mm"
include "wb.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "psssstrd.mm"
include "lcv2.mm"
include "lcvnbtwn2.mm"
include "sseqtr4d.mm"

theorem lsatexch
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  assume lsatexch.s: |- S = ( LSubSp ` W )
  assume lsatexch.p: |- .(+) = ( LSSum ` W )
  assume lsatexch.o: |- .0. = ( 0g ` W )
  assume lsatexch.a: |- A = ( LSAtoms ` W )
  assume lsatexch.w: |- ( ph -> W e. LVec )
  assume lsatexch.u: |- ( ph -> U e. S )
  assume lsatexch.q: |- ( ph -> Q e. A )
  assume lsatexch.r: |- ( ph -> R e. A )
  assume lsatexch.l: |- ( ph -> Q C_ ( U .(+) R ) )
  assume lsatexch.z: |- ( ph -> ( U i^i Q ) = { .0. } )


  assert |- ( ph -> R C_ ( U .(+) Q ) )

  proof
    wph
    cR
    cU
    cR
    c.po
    co
    #
    cU
    cQ
    c.po
    co
    #
    wph
    cU
    cW
    csubg
    cfv
    #
    wcel
    #
    cR
    @2
    wcel
    #
    cR
    @0
    wss
    wph
    cS
    @2
    cU
    wph
    cW
    clmod
    wcel
    #
    cS
    @2
    wss
    wph
    cW
    clvec
    wcel
    @5
    lsatexch.w
    cW
    lveclmod
    syl
    #
    cS
    cW
    lsatexch.s
    lsssssubg
    syl
    #
    lsatexch.u
    sseldd
    #
    wph
    cS
    @2
    cR
    @7
    wph
    cA
    cS
    cR
    cW
    lsatexch.s
    lsatexch.a
    @6
    lsatexch.r
    lsatlssel
    #
    sseldd
    #
    c.po
    cU
    cR
    cW
    lsatexch.p
    lsmub2
    syl2anc
    wph
    cW
    clcv
    cfv
    #
    cU
    cS
    @0
    @1
    cW
    clvec
    lsatexch.s
    @11
    eqid
    #
    lsatexch.w
    lsatexch.u
    wph
    @5
    cU
    cS
    wcel
    #
    cR
    cS
    wcel
    @0
    cS
    wcel
    @6
    lsatexch.u
    @9
    c.po
    cS
    cU
    cR
    cW
    lsatexch.s
    lsatexch.p
    lsmcl
    syl3anc
    #
    wph
    @5
    @13
    cQ
    cS
    wcel
    @1
    cS
    wcel
    @6
    lsatexch.u
    wph
    cA
    cS
    cQ
    cW
    lsatexch.s
    lsatexch.a
    @6
    lsatexch.q
    lsatlssel
    #
    c.po
    cS
    cU
    cQ
    cW
    lsatexch.s
    lsatexch.p
    lsmcl
    syl3anc
    #
    wph
    cU
    @0
    wpss
    cU
    @0
    @11
    wbr
    wph
    cU
    @1
    @0
    wph
    @11
    cS
    cU
    @1
    cW
    clvec
    lsatexch.s
    @12
    lsatexch.w
    lsatexch.u
    @16
    wph
    cU
    cQ
    cin
    c.0
    csn
    wceq
    cU
    @1
    @11
    wbr
    lsatexch.z
    wph
    cA
    @11
    c.po
    cQ
    cS
    cU
    cW
    c.0
    lsatexch.s
    lsatexch.p
    lsatexch.o
    lsatexch.a
    @12
    lsatexch.w
    lsatexch.u
    lsatexch.q
    lcvp
    mpbid
    lcvpss
    #
    wph
    cU
    @0
    wss
    #
    cQ
    @0
    wss
    #
    @1
    @0
    wss
    #
    wph
    @3
    @4
    @18
    @8
    @10
    c.po
    cU
    cR
    cW
    lsatexch.p
    lsmub1
    syl2anc
    lsatexch.l
    wph
    @3
    cQ
    @2
    wcel
    @0
    @2
    wcel
    @18
    @19
    wa
    @20
    wb
    @8
    wph
    cS
    @2
    cQ
    @7
    @15
    sseldd
    wph
    cS
    @2
    @0
    @7
    @14
    sseldd
    c.po
    cU
    cQ
    @0
    cW
    lsatexch.p
    lsmlub
    syl3anc
    mpbi2and
    #
    psssstrd
    wph
    cA
    @11
    c.po
    cR
    cS
    cU
    cW
    lsatexch.s
    lsatexch.p
    lsatexch.a
    @12
    lsatexch.w
    lsatexch.u
    lsatexch.r
    lcv2
    mpbid
    @17
    @21
    lcvnbtwn2
    sseqtr4d
end
