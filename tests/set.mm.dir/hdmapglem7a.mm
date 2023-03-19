include "cv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cfv.mm"
include "wrex.mm"
include "wcel.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "c0g.mm"
include "cbs.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "snssd.mm"
include "dochocsp.mm"
include "fveq2d.mm"
include "dochocsn.mm"
include "eqtrd.mm"
include "dochexmid.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "csubg.mm"
include "wb.mm"
include "wss.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "chlt.mm"
include "wa.mm"
include "dochlss.mm"
include "lsmelval.mm"
include "mpbid.mm"
include "rexcom.mm"
include "wex.mm"
include "df-rex.mm"
include "lspsnel.mm"
include "anbi1d.mm"
include "r19.41v.mm"
include "syl6bbr.mm"
include "exbidv.mm"
include "rexcom4.mm"
include "ovex.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "rexbidv.mm"

theorem hdmapglem7a
  let wph: wff ph
  let vu: setvar u
  let cB: class B
  let c.pl: class .+
  let c.po: class .(+)
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cE: class E
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vl: setvar l
  let vv: setvar v
  let cG: class G
  let cS: class S
  let cY: class Y
  assume hdmapglem7.h: |- H = ( LHyp ` K )
  assume hdmapglem7.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapglem7.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapglem7.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapglem7.v: |- V = ( Base ` U )
  assume hdmapglem7.p: |- .+ = ( +g ` U )
  assume hdmapglem7.q: |- .x. = ( .s ` U )
  assume hdmapglem7.r: |- R = ( Scalar ` U )
  assume hdmapglem7.b: |- B = ( Base ` R )
  assume hdmapglem7.a: |- .(+) = ( LSSum ` U )
  assume hdmapglem7.n: |- N = ( LSpan ` U )
  assume hdmapglem7.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapglem7.x: |- ( ph -> X e. V )

  disjoint k u
  disjoint .+ k
  disjoint .+ u
  disjoint B k
  disjoint B u
  disjoint E k
  disjoint E u
  disjoint N k
  disjoint N u
  disjoint O k
  disjoint O u
  disjoint .x. k
  disjoint .x. u
  disjoint R k
  disjoint U k
  disjoint U u
  disjoint V k
  disjoint X k
  disjoint X u
  disjoint k ph
  disjoint ph u
  disjoint a k
  disjoint a l
  disjoint a u
  disjoint a v
  disjoint .+ a
  disjoint k l
  disjoint k v
  disjoint l u
  disjoint l v
  disjoint .+ l
  disjoint u v
  disjoint .+ v
  disjoint B a
  disjoint B l
  disjoint B v
  disjoint E a
  disjoint E l
  disjoint E v
  disjoint G k
  disjoint G l
  disjoint G u
  disjoint G v
  disjoint N a
  disjoint N l
  disjoint N v
  disjoint O a
  disjoint O l
  disjoint O v
  disjoint .x. a
  disjoint .x. l
  disjoint .x. v
  disjoint R l
  disjoint S k
  disjoint S l
  disjoint S u
  disjoint S v
  disjoint U a
  disjoint U l
  disjoint U v
  disjoint V l
  disjoint X a
  disjoint X l
  disjoint X v
  disjoint Y k
  disjoint Y l
  disjoint Y u
  disjoint Y v
  disjoint a ph
  disjoint l ph
  disjoint ph v
  assert |- ( ph -> E. u e. ( O ` { E } ) E. k e. B X = ( ( k .x. E ) .+ u ) )

  proof
    wph
    cX
    va
    cv
    #
    vu
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vu
    cE
    csn
    #
    cO
    cfv
    #
    wrex
    va
    @4
    cN
    cfv
    #
    wrex
    #
    cX
    vk
    cv
    #
    cE
    c.x
    co
    #
    @1
    c.pl
    co
    #
    wceq
    #
    vk
    cB
    wrex
    #
    vu
    @5
    wrex
    #
    wph
    cX
    @6
    @5
    c.po
    co
    #
    wcel
    #
    @7
    wph
    cX
    cV
    @14
    hdmapglem7.x
    wph
    @6
    @6
    cO
    cfv
    #
    c.po
    co
    cV
    @14
    wph
    c.po
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    cO
    cV
    cW
    @6
    hdmapglem7.h
    hdmapglem7.o
    hdmapglem7.u
    hdmapglem7.v
    @17
    eqid
    #
    hdmapglem7.a
    hdmapglem7.k
    wph
    cU
    clmod
    wcel
    #
    cE
    cV
    wcel
    #
    @6
    @17
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.k
    dvhlmod
    #
    wph
    cE
    cV
    cU
    c0g
    cfv
    #
    csn
    wph
    cK
    cbs
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cE
    cH
    cK
    cV
    cW
    @22
    hdmapglem7.h
    @23
    eqid
    @24
    eqid
    hdmapglem7.u
    hdmapglem7.v
    @22
    eqid
    hdmapglem7.e
    hdmapglem7.k
    dvheveccl
    eldifad
    #
    @17
    cN
    cV
    cU
    cE
    hdmapglem7.v
    @18
    hdmapglem7.n
    lspsncl
    syl2anc
    #
    wph
    @16
    cO
    cfv
    @5
    cO
    cfv
    @6
    wph
    @16
    @5
    cO
    wph
    cU
    cH
    cK
    cN
    cO
    cV
    cW
    @4
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.o
    hdmapglem7.v
    hdmapglem7.n
    hdmapglem7.k
    wph
    cE
    cV
    @25
    snssd
    #
    dochocsp
    #
    fveq2d
    wph
    cU
    cH
    cK
    cN
    cO
    cV
    cW
    cE
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.o
    hdmapglem7.v
    hdmapglem7.n
    hdmapglem7.k
    @25
    dochocsn
    eqtrd
    dochexmid
    wph
    @16
    @5
    @6
    c.po
    @28
    oveq2d
    eqtr3d
    eleqtrd
    wph
    @6
    cU
    csubg
    cfv
    #
    wcel
    @5
    @29
    wcel
    @15
    @7
    wb
    wph
    @17
    @29
    @6
    wph
    @19
    @17
    @29
    wss
    @21
    @17
    cU
    @18
    lsssssubg
    syl
    #
    @26
    sseldd
    wph
    @17
    @29
    @5
    @30
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @4
    cV
    wss
    @5
    @17
    wcel
    hdmapglem7.k
    @27
    @17
    cU
    cH
    cK
    cO
    cV
    cW
    @4
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.v
    @18
    hdmapglem7.o
    dochlss
    syl2anc
    sseldd
    va
    vu
    c.pl
    c.po
    @6
    @5
    cU
    cX
    hdmapglem7.p
    hdmapglem7.a
    lsmelval
    syl2anc
    mpbid
    @7
    @3
    va
    @6
    wrex
    #
    vu
    @5
    wrex
    wph
    @13
    @3
    va
    vu
    @6
    @5
    rexcom
    wph
    @31
    @12
    vu
    @5
    @31
    @0
    @6
    wcel
    #
    @3
    wa
    #
    va
    wex
    #
    wph
    @12
    @3
    va
    @6
    df-rex
    wph
    @34
    @0
    @9
    wceq
    #
    @3
    wa
    #
    vk
    cB
    wrex
    #
    va
    wex
    #
    @12
    wph
    @33
    @37
    va
    wph
    @33
    @35
    vk
    cB
    wrex
    #
    @3
    wa
    @37
    wph
    @32
    @39
    @3
    wph
    @19
    @20
    @32
    @39
    wb
    @21
    @25
    c.x
    @0
    vk
    cR
    cB
    cN
    cV
    cU
    cE
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.v
    hdmapglem7.q
    hdmapglem7.n
    lspsnel
    syl2anc
    anbi1d
    @35
    @3
    vk
    cB
    r19.41v
    syl6bbr
    exbidv
    @38
    @36
    va
    wex
    #
    vk
    cB
    wrex
    @12
    @36
    vk
    va
    cB
    rexcom4
    @40
    @11
    vk
    cB
    @3
    @11
    va
    @9
    @8
    cE
    c.x
    ovex
    @35
    @2
    @10
    cX
    @0
    @9
    @1
    c.pl
    oveq1
    eqeq2d
    ceqsexv
    rexbii
    bitr3i
    syl6bb
    syl5bb
    rexbidv
    syl5bb
    mpbid
end
