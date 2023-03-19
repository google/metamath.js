include "ccnv.mm"
include "cfv.mm"
include "cp0.mm"
include "wne.mm"
include "csn.mm"
include "cjn.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "catm.mm"
include "wrex.mm"
include "wss.mm"
include "cdif.mm"
include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "wi.mm"
include "simpld.mm"
include "crn.mm"
include "eqid.mm"
include "dihcnvcl.mm"
include "syl2anc.mm"
include "eldifad.mm"
include "eldifsni.mm"
include "syl.mm"
include "dihlspsnat.mm"
include "syl3anc.mm"
include "cvrat42.mm"
include "syl13anc.mm"
include "dih0sb.mm"
include "necon3bid.mm"
include "dihlsprn.mm"
include "dihrnss.mm"
include "djhcl.mm"
include "syl12anc.mm"
include "dihcnvord.mm"
include "djhj.mm"
include "breq2d.mm"
include "bitr3d.mm"
include "anbi12d.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "dihatexv2.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "oveq1.mm"
include "rexxfr2d.mm"
include "rexbidva.mm"
include "bitr2d.mm"
include "3imtr4d.mm"

theorem djhcvat42
  let wph: wff ph
  let vz: setvar z
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vr: setvar r
  assume djhcvat42.h: |- H = ( LHyp ` K )
  assume djhcvat42.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhcvat42.v: |- V = ( Base ` U )
  assume djhcvat42.o: |- .0. = ( 0g ` U )
  assume djhcvat42.n: |- N = ( LSpan ` U )
  assume djhcvat42.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djhcvat42.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djhcvat42.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhcvat42.s: |- ( ph -> S e. ran I )
  assume djhcvat42.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume djhcvat42.y: |- ( ph -> Y e. ( V \ { .0. } ) )

  disjoint I z
  disjoint K z
  disjoint N z
  disjoint ph z
  disjoint W z
  disjoint S z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint .0. r
  disjoint r z
  disjoint I r
  disjoint K r
  disjoint N r
  disjoint ph r
  disjoint S r
  disjoint V r
  disjoint X r
  disjoint Y r
  assert |- ( ph -> ( ( S =/= { .0. } /\ ( N ` { X } ) C_ ( S .\/ ( N ` { Y } ) ) ) -> E. z e. ( V \ { .0. } ) ( ( N ` { z } ) C_ S /\ ( N ` { X } ) C_ ( ( N ` { z } ) .\/ ( N ` { Y } ) ) ) ) )

  proof
    wph
    cS
    cI
    ccnv
    #
    cfv
    #
    cK
    cp0
    cfv
    #
    wne
    #
    cX
    csn
    cN
    cfv
    #
    @0
    cfv
    #
    @1
    cY
    csn
    cN
    cfv
    #
    @0
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    wa
    #
    vr
    cv
    #
    @1
    @10
    wbr
    #
    @5
    @13
    @7
    @8
    co
    #
    @10
    wbr
    #
    wa
    #
    vr
    cK
    catm
    cfv
    #
    wrex
    #
    cS
    c.0
    csn
    #
    wne
    #
    @4
    cS
    @6
    c.or
    co
    #
    wss
    #
    wa
    vz
    cv
    #
    csn
    cN
    cfv
    #
    cS
    wss
    #
    @4
    @25
    @6
    c.or
    co
    #
    wss
    #
    wa
    #
    vz
    cV
    @20
    cdif
    #
    wrex
    #
    wph
    cK
    chlt
    wcel
    #
    @1
    cK
    cbs
    cfv
    #
    wcel
    #
    @5
    @18
    wcel
    #
    @7
    @18
    wcel
    #
    @12
    @19
    wi
    wph
    @32
    cW
    cH
    wcel
    #
    djhcvat42.k
    simpld
    wph
    @32
    @37
    wa
    #
    cS
    cI
    crn
    #
    wcel
    #
    @34
    djhcvat42.k
    djhcvat42.s
    @33
    cH
    cI
    cK
    cW
    cS
    @33
    eqid
    #
    djhcvat42.h
    djhcvat42.i
    dihcnvcl
    syl2anc
    wph
    @38
    cX
    cV
    wcel
    #
    cX
    c.0
    wne
    #
    @35
    djhcvat42.k
    wph
    cX
    cV
    @20
    djhcvat42.x
    eldifad
    #
    wph
    cX
    @30
    wcel
    @43
    djhcvat42.x
    cX
    cV
    c.0
    eldifsni
    syl
    @18
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    c.0
    @18
    eqid
    #
    djhcvat42.h
    djhcvat42.u
    djhcvat42.v
    djhcvat42.o
    djhcvat42.n
    djhcvat42.i
    dihlspsnat
    syl3anc
    wph
    @38
    cY
    cV
    wcel
    #
    cY
    c.0
    wne
    #
    @36
    djhcvat42.k
    wph
    cY
    cV
    @20
    djhcvat42.y
    eldifad
    #
    wph
    cY
    @30
    wcel
    @47
    djhcvat42.y
    cY
    cV
    c.0
    eldifsni
    syl
    @18
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cY
    c.0
    @45
    djhcvat42.h
    djhcvat42.u
    djhcvat42.v
    djhcvat42.o
    djhcvat42.n
    djhcvat42.i
    dihlspsnat
    syl3anc
    @18
    @33
    @5
    @7
    @8
    cK
    @10
    @1
    @2
    vr
    @41
    @10
    eqid
    #
    @8
    eqid
    #
    @2
    eqid
    #
    @45
    cvrat42
    syl13anc
    wph
    @21
    @3
    @23
    @11
    wph
    cS
    @20
    @1
    @2
    wph
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cS
    @2
    c.0
    djhcvat42.h
    @51
    djhcvat42.i
    djhcvat42.u
    djhcvat42.v
    djhcvat42.o
    djhcvat42.n
    djhcvat42.k
    djhcvat42.s
    dih0sb
    necon3bid
    wph
    @5
    @22
    @0
    cfv
    #
    @10
    wbr
    @23
    @11
    wph
    cH
    cI
    cK
    @10
    cW
    @4
    @22
    @49
    djhcvat42.h
    djhcvat42.i
    djhcvat42.k
    wph
    @38
    @42
    @4
    @39
    wcel
    #
    djhcvat42.k
    @44
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    djhcvat42.h
    djhcvat42.u
    djhcvat42.v
    djhcvat42.n
    djhcvat42.i
    dihlsprn
    #
    syl2anc
    wph
    @38
    cS
    cV
    wss
    #
    @6
    cV
    wss
    #
    @22
    @39
    wcel
    djhcvat42.k
    wph
    @38
    @40
    @55
    djhcvat42.k
    djhcvat42.s
    cU
    cH
    cI
    cK
    cV
    cW
    cS
    djhcvat42.h
    djhcvat42.u
    djhcvat42.i
    djhcvat42.v
    dihrnss
    syl2anc
    wph
    @38
    @6
    @39
    wcel
    #
    @56
    djhcvat42.k
    wph
    @38
    @46
    @57
    djhcvat42.k
    @48
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cY
    djhcvat42.h
    djhcvat42.u
    djhcvat42.v
    djhcvat42.n
    djhcvat42.i
    dihlsprn
    syl2anc
    #
    cU
    cH
    cI
    cK
    cV
    cW
    @6
    djhcvat42.h
    djhcvat42.u
    djhcvat42.i
    djhcvat42.v
    dihrnss
    syl2anc
    #
    cU
    cH
    cI
    c.or
    cK
    cV
    cW
    cS
    @6
    djhcvat42.h
    djhcvat42.i
    djhcvat42.u
    djhcvat42.v
    djhcvat42.j
    djhcl
    syl12anc
    dihcnvord
    wph
    @52
    @9
    @5
    @10
    wph
    cH
    cI
    c.or
    @8
    cK
    cW
    cS
    @6
    @50
    djhcvat42.h
    djhcvat42.i
    djhcvat42.j
    djhcvat42.k
    djhcvat42.s
    @58
    djhj
    breq2d
    bitr3d
    anbi12d
    wph
    @19
    @25
    @0
    cfv
    #
    @1
    @10
    wbr
    #
    @5
    @60
    @7
    @8
    co
    #
    @10
    wbr
    #
    wa
    #
    vz
    @30
    wrex
    @31
    wph
    @17
    @64
    vr
    vz
    @60
    @18
    @30
    @18
    wph
    @24
    @30
    wcel
    #
    wa
    #
    @38
    @24
    cV
    wcel
    #
    @24
    c.0
    wne
    #
    @60
    @18
    wcel
    wph
    @38
    @65
    djhcvat42.k
    adantr
    #
    @65
    @67
    wph
    @24
    cV
    @20
    eldifi
    adantl
    #
    @65
    @68
    wph
    @24
    cV
    c.0
    eldifsni
    adantl
    @18
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    @24
    c.0
    @45
    djhcvat42.h
    djhcvat42.u
    djhcvat42.v
    djhcvat42.o
    djhcvat42.n
    djhcvat42.i
    dihlspsnat
    syl3anc
    wph
    vz
    @18
    @13
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    c.0
    @45
    djhcvat42.h
    djhcvat42.u
    djhcvat42.v
    djhcvat42.o
    djhcvat42.n
    djhcvat42.i
    djhcvat42.k
    dihatexv2
    @13
    @60
    wceq
    #
    @17
    @64
    wb
    wph
    @71
    @14
    @61
    @16
    @63
    @13
    @60
    @1
    @10
    breq1
    @71
    @15
    @62
    @5
    @10
    @13
    @60
    @7
    @8
    oveq1
    breq2d
    anbi12d
    adantl
    rexxfr2d
    wph
    @64
    @29
    vz
    @30
    @66
    @61
    @26
    @63
    @28
    @66
    cH
    cI
    cK
    @10
    cW
    @25
    cS
    @49
    djhcvat42.h
    djhcvat42.i
    @69
    @66
    @38
    @67
    @25
    @39
    wcel
    #
    @69
    @70
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    @24
    djhcvat42.h
    djhcvat42.u
    djhcvat42.v
    djhcvat42.n
    djhcvat42.i
    dihlsprn
    syl2anc
    #
    wph
    @40
    @65
    djhcvat42.s
    adantr
    dihcnvord
    @66
    @5
    @27
    @0
    cfv
    #
    @10
    wbr
    @63
    @28
    @66
    @74
    @62
    @5
    @10
    @66
    cH
    cI
    c.or
    @8
    cK
    cW
    @25
    @6
    @50
    djhcvat42.h
    djhcvat42.i
    djhcvat42.j
    @69
    @73
    wph
    @57
    @65
    @58
    adantr
    djhj
    breq2d
    @66
    cH
    cI
    cK
    @10
    cW
    @4
    @27
    @49
    djhcvat42.h
    djhcvat42.i
    @69
    @66
    @38
    @42
    @53
    @69
    wph
    @42
    @65
    @44
    adantr
    @54
    syl2anc
    @66
    @38
    @25
    cV
    wss
    #
    @56
    @27
    @39
    wcel
    @69
    @66
    @38
    @72
    @75
    @69
    @73
    cU
    cH
    cI
    cK
    cV
    cW
    @25
    djhcvat42.h
    djhcvat42.u
    djhcvat42.i
    djhcvat42.v
    dihrnss
    syl2anc
    wph
    @56
    @65
    @59
    adantr
    cU
    cH
    cI
    c.or
    cK
    cV
    cW
    @25
    @6
    djhcvat42.h
    djhcvat42.i
    djhcvat42.u
    djhcvat42.v
    djhcvat42.j
    djhcl
    syl12anc
    dihcnvord
    bitr3d
    anbi12d
    rexbidva
    bitr2d
    3imtr4d
end
