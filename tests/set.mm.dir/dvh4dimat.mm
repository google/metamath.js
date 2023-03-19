include "cv.mm"
include "co.mm"
include "wss.mm"
include "wn.mm"
include "wrex.mm"
include "cdih.mm"
include "cfv.mm"
include "catm.mm"
include "ccnv.mm"
include "cjn.mm"
include "cple.mm"
include "wbr.mm"
include "chlt.mm"
include "wcel.mm"
include "simpld.mm"
include "wa.mm"
include "eqid.mm"
include "dihlatat.mm"
include "syl2anc.mm"
include "3dim3.mm"
include "syl13anc.mm"
include "adantr.mm"
include "crn.mm"
include "dih1dimat.mm"
include "dihsmatrn.mm"
include "dihjat4.mm"
include "dihjat6.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "sseq2d.mm"
include "cbs.mm"
include "wb.mm"
include "atbase.mm"
include "adantl.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "dihord.mm"
include "bitr2d.mm"
include "notbid.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "dihatlat.mm"
include "sylan.mm"
include "wceq.mm"
include "dihcnvid2.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sseq1.mm"
include "rexxfrd.mm"
include "mpbird.mm"

theorem dvh4dimat
  let wph: wff ph
  let cA: class A
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  assume dvh4dimat.h: |- H = ( LHyp ` K )
  assume dvh4dimat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh4dimat.s: |- .(+) = ( LSSum ` U )
  assume dvh4dimat.a: |- A = ( LSAtoms ` U )
  assume dvh4dimat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh4dimat.p: |- ( ph -> P e. A )
  assume dvh4dimat.q: |- ( ph -> Q e. A )
  assume dvh4dimat.r: |- ( ph -> R e. A )

  disjoint A s
  disjoint K s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint .(+) s
  disjoint W s
  disjoint ph s
  disjoint r s
  disjoint A r
  disjoint K r
  disjoint P r
  disjoint Q r
  disjoint R r
  disjoint .(+) r
  disjoint W r
  disjoint ph r
  assert |- ( ph -> E. s e. A -. s C_ ( ( P .(+) Q ) .(+) R ) )

  proof
    wph
    vs
    cv
    #
    cP
    cQ
    c.po
    co
    #
    cR
    c.po
    co
    #
    wss
    #
    wn
    #
    vs
    cA
    wrex
    vr
    cv
    #
    cW
    cK
    cdih
    cfv
    cfv
    #
    cfv
    #
    @2
    wss
    #
    wn
    #
    vr
    cK
    catm
    cfv
    #
    wrex
    #
    wph
    @5
    cP
    @6
    ccnv
    #
    cfv
    #
    cQ
    @12
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cR
    @12
    cfv
    #
    @15
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    wn
    #
    vr
    @10
    wrex
    #
    @11
    wph
    cK
    chlt
    wcel
    #
    @13
    @10
    wcel
    #
    @14
    @10
    wcel
    #
    @17
    @10
    wcel
    #
    @22
    wph
    @23
    cW
    cH
    wcel
    #
    dvh4dimat.k
    simpld
    #
    wph
    @23
    @27
    wa
    #
    cP
    cA
    wcel
    #
    @24
    dvh4dimat.k
    dvh4dimat.p
    @10
    cP
    cU
    cH
    @6
    cK
    cA
    cW
    @10
    eqid
    #
    dvh4dimat.h
    dvh4dimat.u
    @6
    eqid
    #
    dvh4dimat.a
    dihlatat
    syl2anc
    #
    wph
    @29
    cQ
    cA
    wcel
    #
    @25
    dvh4dimat.k
    dvh4dimat.q
    @10
    cQ
    cU
    cH
    @6
    cK
    cA
    cW
    @31
    dvh4dimat.h
    dvh4dimat.u
    @32
    dvh4dimat.a
    dihlatat
    syl2anc
    #
    wph
    @29
    cR
    cA
    wcel
    #
    @26
    dvh4dimat.k
    dvh4dimat.r
    @10
    cR
    cU
    cH
    @6
    cK
    cA
    cW
    @31
    dvh4dimat.h
    dvh4dimat.u
    @32
    dvh4dimat.a
    dihlatat
    syl2anc
    #
    @10
    @13
    @14
    @17
    @15
    cK
    @19
    vr
    @15
    eqid
    #
    @19
    eqid
    #
    @31
    3dim3
    syl13anc
    wph
    @21
    @9
    vr
    @10
    wph
    @5
    @10
    wcel
    #
    wa
    #
    @20
    @8
    @41
    @8
    @7
    @18
    @6
    cfv
    #
    wss
    #
    @20
    @41
    @2
    @42
    @7
    @41
    @2
    @1
    @12
    cfv
    #
    @17
    @15
    co
    #
    @6
    cfv
    @42
    @41
    cA
    c.po
    cR
    cU
    cH
    @6
    @15
    cK
    cW
    @1
    @38
    dvh4dimat.h
    @32
    dvh4dimat.u
    dvh4dimat.s
    dvh4dimat.a
    wph
    @29
    @40
    dvh4dimat.k
    adantr
    #
    wph
    @1
    @6
    crn
    #
    wcel
    @40
    wph
    cA
    c.po
    cQ
    cU
    cH
    @6
    cK
    cW
    cP
    dvh4dimat.h
    @32
    dvh4dimat.u
    dvh4dimat.s
    dvh4dimat.a
    dvh4dimat.k
    wph
    @29
    @30
    cP
    @47
    wcel
    #
    dvh4dimat.k
    dvh4dimat.p
    cA
    cP
    cU
    cH
    @6
    cK
    cW
    dvh4dimat.h
    dvh4dimat.u
    @32
    dvh4dimat.a
    dih1dimat
    syl2anc
    #
    dvh4dimat.q
    dihsmatrn
    adantr
    wph
    @36
    @40
    dvh4dimat.r
    adantr
    dihjat4
    @41
    @45
    @18
    @6
    @41
    @44
    @16
    @17
    @15
    @41
    cA
    c.po
    cQ
    cU
    cH
    @6
    @15
    cK
    cW
    cP
    @38
    dvh4dimat.h
    @32
    dvh4dimat.u
    dvh4dimat.s
    dvh4dimat.a
    @46
    wph
    @48
    @40
    @49
    adantr
    wph
    @34
    @40
    dvh4dimat.q
    adantr
    dihjat6
    oveq1d
    fveq2d
    eqtrd
    sseq2d
    @41
    @29
    @5
    cK
    cbs
    cfv
    #
    wcel
    #
    @18
    @50
    wcel
    #
    @43
    @20
    wb
    @46
    @40
    @51
    wph
    @10
    @50
    @5
    cK
    @50
    eqid
    #
    @31
    atbase
    adantl
    wph
    @52
    @40
    wph
    cK
    clat
    wcel
    #
    @16
    @50
    wcel
    #
    @17
    @50
    wcel
    #
    @52
    wph
    @23
    @54
    @28
    cK
    hllat
    syl
    wph
    @23
    @24
    @25
    @55
    @28
    @33
    @35
    @10
    @50
    @15
    cK
    @13
    @14
    @53
    @38
    @31
    hlatjcl
    syl3anc
    wph
    @26
    @56
    @37
    @10
    @50
    @17
    cK
    @53
    @31
    atbase
    syl
    @50
    @15
    cK
    @16
    @17
    @53
    @38
    latjcl
    syl3anc
    adantr
    @50
    cH
    @6
    cK
    @19
    cW
    @5
    @18
    @53
    @39
    dvh4dimat.h
    @32
    dihord
    syl3anc
    bitr2d
    notbid
    rexbidva
    mpbid
    wph
    @4
    @9
    vs
    vr
    @7
    cA
    @10
    wph
    @29
    @40
    @7
    cA
    wcel
    dvh4dimat.k
    @10
    @5
    cU
    cH
    @6
    cK
    cA
    cW
    @31
    dvh4dimat.h
    dvh4dimat.u
    @32
    dvh4dimat.a
    dihatlat
    sylan
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @0
    @12
    cfv
    #
    @10
    wcel
    #
    @0
    @59
    @6
    cfv
    #
    wceq
    #
    @0
    @7
    wceq
    #
    vr
    @10
    wrex
    wph
    @29
    @57
    @60
    dvh4dimat.k
    @10
    @0
    cU
    cH
    @6
    cK
    cA
    cW
    @31
    dvh4dimat.h
    dvh4dimat.u
    @32
    dvh4dimat.a
    dihlatat
    sylan
    @58
    @61
    @0
    @58
    @29
    @0
    @47
    wcel
    #
    @61
    @0
    wceq
    wph
    @29
    @57
    dvh4dimat.k
    adantr
    wph
    @29
    @57
    @64
    dvh4dimat.k
    cA
    @0
    cU
    cH
    @6
    cK
    cW
    dvh4dimat.h
    dvh4dimat.u
    @32
    dvh4dimat.a
    dih1dimat
    sylan
    cH
    @6
    cK
    cW
    @0
    dvh4dimat.h
    @32
    dihcnvid2
    syl2anc
    eqcomd
    @63
    @62
    vr
    @59
    @10
    @5
    @59
    wceq
    @7
    @61
    @0
    @5
    @59
    @6
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @63
    @4
    @9
    wb
    wph
    @63
    @3
    @8
    @0
    @7
    @2
    sseq1
    notbid
    adantl
    rexxfrd
    mpbird
end
