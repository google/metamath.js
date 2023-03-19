include "co.mm"
include "cfv.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wrel.mm"
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
include "eqid.mm"
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

theorem dib2dim
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
  assume dib2dim.l: |- .<_ = ( le ` K )
  assume dib2dim.j: |- .\/ = ( join ` K )
  assume dib2dim.a: |- A = ( Atoms ` K )
  assume dib2dim.h: |- H = ( LHyp ` K )
  assume dib2dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dib2dim.s: |- .(+) = ( LSSum ` U )
  assume dib2dim.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dib2dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dib2dim.p: |- ( ph -> ( P e. A /\ P .<_ W ) )
  assume dib2dim.q: |- ( ph -> ( Q e. A /\ Q .<_ W ) )


  assert |- ( ph -> ( I ` ( P .\/ Q ) ) C_ ( ( I ` P ) .(+) ( I ` Q ) ) )

  proof
    wph
    vf
    vs
    cP
    cQ
    c.or
    co
    #
    cI
    cfv
    #
    cP
    cI
    cfv
    cQ
    cI
    cfv
    c.po
    co
    #
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
    @1
    wrel
    dib2dim.k
    cH
    cI
    cK
    chlt
    cW
    @0
    dib2dim.h
    dib2dim.i
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
    @6
    cP
    @7
    cfv
    cQ
    @7
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
    @14
    wa
    @6
    @10
    cop
    #
    @1
    wcel
    #
    @20
    @2
    wcel
    wph
    @9
    @19
    @14
    wph
    @8
    @18
    @6
    wph
    cA
    @17
    cP
    cH
    @7
    c.or
    cK
    c.le
    cQ
    cW
    @16
    dib2dim.l
    dib2dim.j
    dib2dim.a
    dib2dim.h
    @16
    eqid
    #
    @17
    eqid
    #
    @7
    eqid
    #
    dib2dim.k
    dib2dim.p
    dib2dim.q
    dia2dim
    sseld
    anim1d
    wph
    @5
    @0
    @12
    wcel
    #
    @0
    cW
    c.le
    wbr
    #
    @21
    @15
    wb
    dib2dim.k
    wph
    @3
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    @25
    wph
    @3
    @4
    dib2dim.k
    simpld
    #
    wph
    @27
    cP
    cW
    c.le
    wbr
    #
    dib2dim.p
    simpld
    #
    wph
    @28
    cQ
    cW
    c.le
    wbr
    #
    dib2dim.q
    simpld
    #
    cA
    @12
    c.or
    cK
    cP
    cQ
    @12
    eqid
    #
    dib2dim.j
    dib2dim.a
    hlatjcl
    syl3anc
    wph
    @30
    @32
    @26
    wph
    @27
    @30
    dib2dim.p
    simprd
    #
    wph
    @28
    @32
    dib2dim.q
    simprd
    #
    wph
    cK
    clat
    wcel
    #
    cP
    @12
    wcel
    #
    cQ
    @12
    wcel
    #
    cW
    @12
    wcel
    #
    @30
    @32
    wa
    @26
    wb
    wph
    @3
    @37
    @29
    cK
    hllat
    syl
    wph
    @27
    @38
    @31
    cA
    @12
    cP
    cK
    @34
    dib2dim.a
    atbase
    syl
    #
    wph
    @28
    @39
    @33
    cA
    @12
    cQ
    cK
    @34
    dib2dim.a
    atbase
    syl
    #
    wph
    @4
    @40
    wph
    @3
    @4
    dib2dim.k
    simprd
    @12
    cH
    cK
    cW
    @34
    dib2dim.h
    lhpbase
    syl
    @12
    c.or
    cK
    c.le
    cP
    cQ
    cW
    @34
    dib2dim.l
    dib2dim.j
    latjle12
    syl13anc
    mpbi2and
    @12
    @10
    @11
    vf
    @6
    cH
    cI
    @7
    cK
    c.le
    chlt
    cW
    @0
    @13
    @34
    dib2dim.l
    dib2dim.h
    @11
    eqid
    #
    @13
    eqid
    #
    @24
    dib2dim.i
    dibopelval2
    syl12anc
    wph
    @12
    c.po
    @17
    @10
    @11
    cU
    vf
    @6
    cH
    cI
    @7
    cK
    c.le
    @13
    @16
    cW
    cP
    cQ
    @34
    dib2dim.l
    dib2dim.h
    @43
    @44
    @22
    dib2dim.u
    @23
    dib2dim.s
    @24
    dib2dim.i
    dib2dim.k
    wph
    @38
    @30
    @41
    @35
    jca
    wph
    @39
    @32
    @42
    @36
    jca
    diblsmopel
    3imtr4d
    relssdv
end
