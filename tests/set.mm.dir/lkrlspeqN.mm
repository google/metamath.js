include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "csn.mm"
include "wcel.mm"
include "eldifad.mm"
include "clmod.mm"
include "wb.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lduallmod.mm"
include "eqid.mm"
include "ldualelvbase.mm"
include "lspsnel.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ldualsbase.mm"
include "rexeqdv.mm"
include "w3a.mm"
include "c0g.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "cdif.mm"
include "simp2.mm"
include "simp3.mm"
include "eldifsni.mm"
include "eqnetrrd.mm"
include "wo.mm"
include "ldual0.mm"
include "eqeq2d.mm"
include "orc.mm"
include "syl6bir.mm"
include "lduallvec.mm"
include "eleqtrrd.mm"
include "lvecvs0or.mm"
include "sylibrd.mm"
include "necon3d.mm"
include "mpd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lkreqN.mm"
include "rexlimdv3a.mm"

theorem lkrlspeqN
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cL: class L
  let cN: class N
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  assume lkrlspeq.f: |- F = ( LFnl ` W )
  assume lkrlspeq.l: |- L = ( LKer ` W )
  assume lkrlspeq.d: |- D = ( LDual ` W )
  assume lkrlspeq.o: |- .0. = ( 0g ` D )
  assume lkrlspeq.j: |- N = ( LSpan ` D )
  assume lkrlspeq.w: |- ( ph -> W e. LVec )
  assume lkrlspeq.h: |- ( ph -> H e. F )
  assume lkrlspeq.g: |- ( ph -> G e. ( ( N ` { H } ) \ { .0. } ) )


  assert |- ( ph -> ( L ` G ) = ( L ` H ) )

  proof
    wph
    cG
    vk
    cv
    #
    cH
    cD
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    cG
    cL
    cfv
    cH
    cL
    cfv
    wceq
    #
    wph
    @3
    vk
    cD
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    @6
    wph
    cG
    cH
    csn
    cN
    cfv
    #
    wcel
    #
    @10
    wph
    cG
    @11
    c.0
    csn
    #
    lkrlspeq.g
    eldifad
    wph
    cD
    clmod
    wcel
    cH
    cD
    cbs
    cfv
    #
    wcel
    #
    @12
    @10
    wb
    wph
    cD
    cW
    lkrlspeq.d
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    lkrlspeq.w
    cW
    lveclmod
    syl
    #
    lduallmod
    wph
    cD
    cF
    cH
    @14
    cW
    clvec
    lkrlspeq.f
    lkrlspeq.d
    @14
    eqid
    #
    lkrlspeq.w
    lkrlspeq.h
    ldualelvbase
    #
    @1
    cG
    vk
    @8
    @9
    cN
    @14
    cD
    cH
    @8
    eqid
    #
    @9
    eqid
    #
    @18
    @1
    eqid
    #
    lkrlspeq.j
    lspsnel
    syl2anc
    mpbid
    wph
    @3
    vk
    @9
    @5
    wph
    cD
    @8
    @4
    @9
    @5
    clvec
    cW
    @4
    eqid
    #
    @5
    eqid
    #
    lkrlspeq.d
    @20
    @21
    lkrlspeq.w
    ldualsbase
    #
    rexeqdv
    mpbid
    wph
    @3
    @7
    vk
    @5
    wph
    @0
    @5
    wcel
    #
    @3
    w3a
    #
    @0
    cD
    @5
    @4
    @1
    cF
    cG
    cH
    cL
    cW
    @4
    c0g
    cfv
    #
    @23
    @24
    @28
    eqid
    #
    lkrlspeq.f
    lkrlspeq.l
    lkrlspeq.d
    @22
    wph
    @26
    @16
    @3
    lkrlspeq.w
    3ad2ant1
    @27
    @26
    @0
    @28
    wne
    #
    @0
    @5
    @28
    csn
    cdif
    wcel
    wph
    @26
    @3
    simp2
    #
    @27
    @2
    c.0
    wne
    @30
    @27
    cG
    @2
    c.0
    wph
    @26
    @3
    simp3
    #
    wph
    @26
    cG
    c.0
    wne
    #
    @3
    wph
    cG
    @11
    @13
    cdif
    wcel
    @33
    lkrlspeq.g
    cG
    @11
    c.0
    eldifsni
    syl
    3ad2ant1
    eqnetrrd
    @27
    @0
    @28
    @2
    c.0
    @27
    @0
    @28
    wceq
    #
    @0
    @8
    c0g
    cfv
    #
    wceq
    #
    cH
    c.0
    wceq
    #
    wo
    #
    @2
    c.0
    wceq
    @27
    @34
    @36
    @38
    @27
    @35
    @28
    @0
    wph
    @26
    @35
    @28
    wceq
    @3
    wph
    cD
    @4
    @8
    @35
    cW
    @28
    @23
    @29
    lkrlspeq.d
    @20
    @35
    eqid
    #
    @17
    ldual0
    3ad2ant1
    eqeq2d
    @36
    @37
    orc
    syl6bir
    @27
    @0
    @1
    @8
    @9
    @35
    @14
    cD
    cH
    c.0
    @18
    @22
    @20
    @21
    @39
    lkrlspeq.o
    wph
    @26
    cD
    clvec
    wcel
    @3
    wph
    cD
    cW
    lkrlspeq.d
    lkrlspeq.w
    lduallvec
    3ad2ant1
    @27
    @0
    @5
    @9
    @31
    wph
    @26
    @9
    @5
    wceq
    @3
    @25
    3ad2ant1
    eleqtrrd
    wph
    @26
    @15
    @3
    @19
    3ad2ant1
    lvecvs0or
    sylibrd
    necon3d
    mpd
    @0
    @5
    @28
    eldifsn
    sylanbrc
    wph
    @26
    cH
    cF
    wcel
    @3
    lkrlspeq.h
    3ad2ant1
    @32
    lkreqN
    rexlimdv3a
    mpd
end
