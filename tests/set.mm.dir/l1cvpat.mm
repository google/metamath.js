include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "cdif.mm"
include "wrex.mm"
include "wss.mm"
include "wn.mm"
include "co.mm"
include "wcel.mm"
include "clvec.mm"
include "wb.mm"
include "eqid.mm"
include "islsat.mm"
include "syl.mm"
include "mpbid.mm"
include "wi.mm"
include "eldifi.mm"
include "w3a.mm"
include "clmod.mm"
include "lveclmod.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "lspsnel5.mm"
include "notbid.mm"
include "clsh.mm"
include "wbr.mm"
include "islshpcv.mm"
include "mpbir2and.mm"
include "lshpnelb.mm"
include "biimpd.mm"
include "sylbird.mm"
include "sseq1.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "3exp.mm"
include "syl5.mm"
include "rexlimdv.mm"
include "mp2d.mm"

theorem l1cvpat
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let vv: setvar v
  assume l1cvpat.v: |- V = ( Base ` W )
  assume l1cvpat.s: |- S = ( LSubSp ` W )
  assume l1cvpat.p: |- .(+) = ( LSSum ` W )
  assume l1cvpat.a: |- A = ( LSAtoms ` W )
  assume l1cvpat.c: |- C = ( <oL ` W )
  assume l1cvpat.w: |- ( ph -> W e. LVec )
  assume l1cvpat.u: |- ( ph -> U e. S )
  assume l1cvpat.q: |- ( ph -> Q e. A )
  assume l1cvpat.l: |- ( ph -> U C V )
  assume l1cvpat.m: |- ( ph -> -. Q C_ U )


  assert |- ( ph -> ( U .(+) Q ) = V )

  proof
    wph
    cQ
    vv
    cv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vv
    cV
    cW
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wrex
    #
    cQ
    cU
    wss
    #
    wn
    #
    cU
    cQ
    c.po
    co
    #
    cV
    wceq
    #
    wph
    cQ
    cA
    wcel
    #
    @7
    l1cvpat.q
    wph
    cW
    clvec
    wcel
    #
    @12
    @7
    wb
    l1cvpat.w
    vv
    cA
    cQ
    @1
    cV
    cW
    clvec
    @4
    l1cvpat.v
    @1
    eqid
    #
    @4
    eqid
    l1cvpat.a
    islsat
    syl
    mpbid
    l1cvpat.m
    wph
    @3
    @9
    @11
    wi
    #
    vv
    @6
    @0
    @6
    wcel
    @0
    cV
    wcel
    #
    wph
    @3
    @15
    wi
    @0
    cV
    @5
    eldifi
    wph
    @16
    @3
    @15
    wph
    @16
    @3
    w3a
    #
    @15
    @2
    cU
    wss
    #
    wn
    #
    cU
    @2
    c.po
    co
    #
    cV
    wceq
    #
    wi
    #
    @17
    @19
    @0
    cU
    wcel
    #
    wn
    #
    @21
    @17
    @23
    @18
    @17
    cS
    cU
    @1
    cV
    cW
    @0
    l1cvpat.v
    l1cvpat.s
    @14
    wph
    @16
    cW
    clmod
    wcel
    #
    @3
    wph
    @13
    @25
    l1cvpat.w
    cW
    lveclmod
    syl
    3ad2ant1
    wph
    @16
    cU
    cS
    wcel
    #
    @3
    l1cvpat.u
    3ad2ant1
    wph
    @16
    @3
    simp2
    #
    lspsnel5
    notbid
    @17
    @24
    @21
    @17
    c.po
    cU
    cW
    clsh
    cfv
    #
    @1
    cV
    cW
    @0
    l1cvpat.v
    @14
    l1cvpat.p
    @28
    eqid
    #
    wph
    @16
    @13
    @3
    l1cvpat.w
    3ad2ant1
    wph
    @16
    cU
    @28
    wcel
    #
    @3
    wph
    @30
    @26
    cU
    cV
    cC
    wbr
    l1cvpat.u
    l1cvpat.l
    wph
    cC
    cS
    cU
    @28
    cV
    cW
    l1cvpat.v
    l1cvpat.s
    @29
    l1cvpat.c
    l1cvpat.w
    islshpcv
    mpbir2and
    3ad2ant1
    @27
    lshpnelb
    biimpd
    sylbird
    @3
    wph
    @15
    @22
    wb
    @16
    @3
    @9
    @19
    @11
    @21
    @3
    @8
    @18
    cQ
    @2
    cU
    sseq1
    notbid
    @3
    @10
    @20
    cV
    cQ
    @2
    cU
    c.po
    oveq2
    eqeq1d
    imbi12d
    3ad2ant3
    mpbird
    3exp
    syl5
    rexlimdv
    mp2d
end
