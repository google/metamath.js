include "co.mm"
include "cdib.mm"
include "cfv.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wrel.mm"
include "eqid.mm"
include "dibvalrel.mm"
include "syl.mm"
include "cv.mm"
include "cdia.mm"
include "cltrn.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cmpt.mm"
include "wceq.mm"
include "cdveca.mm"
include "clsm.mm"
include "cop.mm"
include "dia2dim.mm"
include "sseld.mm"
include "anim1d.mm"
include "wbr.mm"
include "wb.mm"
include "simpld.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simprd.mm"
include "clat.mm"
include "hllat.mm"
include "atbase.mm"
include "lhpbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "dibopelval2.mm"
include "syl12anc.mm"
include "jca.mm"
include "diblsmopel.mm"
include "3imtr4d.mm"
include "relssdv.mm"
include "dihvalb.mm"
include "oveq12d.mm"
include "3sstr4d.mm"

theorem dih2dimbALTN
  let wph: wff ph
  let cA: class A
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vf: setvar f
  let vs: setvar s
  assume dih2dimb.l: |- .<_ = ( le ` K )
  assume dih2dimb.j: |- .\/ = ( join ` K )
  assume dih2dimb.a: |- A = ( Atoms ` K )
  assume dih2dimb.h: |- H = ( LHyp ` K )
  assume dih2dimb.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih2dimb.s: |- .(+) = ( LSSum ` U )
  assume dih2dimb.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih2dimb.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dih2dimb.p: |- ( ph -> ( P e. A /\ P .<_ W ) )
  assume dih2dimb.q: |- ( ph -> ( Q e. A /\ Q .<_ W ) )


  assert |- ( ph -> ( I ` ( P .\/ Q ) ) C_ ( ( I ` P ) .(+) ( I ` Q ) ) )

  proof
    wph
    cP
    cQ
    c.or
    co
    #
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    cP
    @1
    cfv
    #
    cQ
    @1
    cfv
    #
    c.po
    co
    #
    @0
    cI
    cfv
    #
    cP
    cI
    cfv
    #
    cQ
    cI
    cfv
    #
    c.po
    co
    wph
    vf
    vs
    @2
    @5
    wph
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    @2
    wrel
    dih2dimb.k
    cH
    @1
    cK
    chlt
    cW
    @0
    dih2dimb.h
    @1
    eqid
    #
    dibvalrel
    syl
    wph
    vf
    cv
    #
    @0
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    wcel
    #
    vs
    cv
    #
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cid
    cK
    cbs
    cfv
    #
    cres
    cmpt
    #
    wceq
    #
    wa
    #
    @13
    cP
    @14
    cfv
    cQ
    @14
    cfv
    cW
    cK
    cdveca
    cfv
    cfv
    #
    clsm
    cfv
    #
    co
    #
    wcel
    #
    @21
    wa
    @13
    @17
    cop
    #
    @2
    wcel
    #
    @27
    @5
    wcel
    wph
    @16
    @26
    @21
    wph
    @15
    @25
    @13
    wph
    cA
    @24
    cP
    cH
    @14
    c.or
    cK
    c.le
    cQ
    cW
    @23
    dih2dimb.l
    dih2dimb.j
    dih2dimb.a
    dih2dimb.h
    @23
    eqid
    #
    @24
    eqid
    #
    @14
    eqid
    #
    dih2dimb.k
    dih2dimb.p
    dih2dimb.q
    dia2dim
    sseld
    anim1d
    wph
    @11
    @0
    @19
    wcel
    #
    @0
    cW
    c.le
    wbr
    #
    @28
    @22
    wb
    dih2dimb.k
    wph
    @9
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    @32
    wph
    @9
    @10
    dih2dimb.k
    simpld
    #
    wph
    @34
    cP
    cW
    c.le
    wbr
    #
    dih2dimb.p
    simpld
    #
    wph
    @35
    cQ
    cW
    c.le
    wbr
    #
    dih2dimb.q
    simpld
    #
    cA
    @19
    c.or
    cK
    cP
    cQ
    @19
    eqid
    #
    dih2dimb.j
    dih2dimb.a
    hlatjcl
    syl3anc
    #
    wph
    @37
    @39
    @33
    wph
    @34
    @37
    dih2dimb.p
    simprd
    #
    wph
    @35
    @39
    dih2dimb.q
    simprd
    #
    wph
    cK
    clat
    wcel
    #
    cP
    @19
    wcel
    #
    cQ
    @19
    wcel
    #
    cW
    @19
    wcel
    #
    @37
    @39
    wa
    @33
    wb
    wph
    @9
    @45
    @36
    cK
    hllat
    syl
    wph
    @34
    @46
    @38
    cA
    @19
    cP
    cK
    @41
    dih2dimb.a
    atbase
    syl
    #
    wph
    @35
    @47
    @40
    cA
    @19
    cQ
    cK
    @41
    dih2dimb.a
    atbase
    syl
    #
    wph
    @10
    @48
    wph
    @9
    @10
    dih2dimb.k
    simprd
    @19
    cH
    cK
    cW
    @41
    dih2dimb.h
    lhpbase
    syl
    @19
    c.or
    cK
    c.le
    cP
    cQ
    cW
    @41
    dih2dimb.l
    dih2dimb.j
    latjle12
    syl13anc
    mpbi2and
    #
    @19
    @17
    @18
    vf
    @13
    cH
    @1
    @14
    cK
    c.le
    chlt
    cW
    @0
    @20
    @41
    dih2dimb.l
    dih2dimb.h
    @18
    eqid
    #
    @20
    eqid
    #
    @31
    @12
    dibopelval2
    syl12anc
    wph
    @19
    c.po
    @24
    @17
    @18
    cU
    vf
    @13
    cH
    @1
    @14
    cK
    c.le
    @20
    @23
    cW
    cP
    cQ
    @41
    dih2dimb.l
    dih2dimb.h
    @52
    @53
    @29
    dih2dimb.u
    @30
    dih2dimb.s
    @31
    @12
    dih2dimb.k
    wph
    @46
    @37
    @49
    @43
    jca
    wph
    @47
    @39
    @50
    @44
    jca
    diblsmopel
    3imtr4d
    relssdv
    wph
    @11
    @32
    @33
    @6
    @2
    wceq
    dih2dimb.k
    @42
    @51
    @19
    @1
    cH
    cI
    cK
    c.le
    chlt
    cW
    @0
    @41
    dih2dimb.l
    dih2dimb.h
    dih2dimb.i
    @12
    dihvalb
    syl12anc
    wph
    @7
    @3
    @8
    @4
    c.po
    wph
    @11
    @46
    @37
    @7
    @3
    wceq
    dih2dimb.k
    @49
    @43
    @19
    @1
    cH
    cI
    cK
    c.le
    chlt
    cW
    cP
    @41
    dih2dimb.l
    dih2dimb.h
    dih2dimb.i
    @12
    dihvalb
    syl12anc
    wph
    @11
    @47
    @39
    @8
    @4
    wceq
    dih2dimb.k
    @50
    @44
    @19
    @1
    cH
    cI
    cK
    c.le
    chlt
    cW
    cQ
    @41
    dih2dimb.l
    dih2dimb.h
    dih2dimb.i
    @12
    dihvalb
    syl12anc
    oveq12d
    3sstr4d
end
