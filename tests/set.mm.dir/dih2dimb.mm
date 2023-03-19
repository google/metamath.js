include "co.mm"
include "cdib.mm"
include "cfv.mm"
include "eqid.mm"
include "dib2dim.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "wbr.mm"
include "wceq.mm"
include "simpld.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simprd.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "lhpbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "dihvalb.mm"
include "syl12anc.mm"
include "oveq12d.mm"
include "3sstr4d.mm"

theorem dih2dimb
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
    cA
    cP
    c.po
    cQ
    cU
    cH
    @1
    c.or
    cK
    c.le
    cW
    dih2dimb.l
    dih2dimb.j
    dih2dimb.a
    dih2dimb.h
    dih2dimb.u
    dih2dimb.s
    @1
    eqid
    #
    dih2dimb.k
    dih2dimb.p
    dih2dimb.q
    dib2dim
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
    @0
    cK
    cbs
    cfv
    #
    wcel
    #
    @0
    cW
    c.le
    wbr
    #
    @5
    @2
    wceq
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
    @13
    wph
    @9
    @10
    dih2dimb.k
    simpld
    #
    wph
    @15
    cP
    cW
    c.le
    wbr
    #
    dih2dimb.p
    simpld
    #
    wph
    @16
    cQ
    cW
    c.le
    wbr
    #
    dih2dimb.q
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
    dih2dimb.j
    dih2dimb.a
    hlatjcl
    syl3anc
    wph
    @18
    @20
    @14
    wph
    @15
    @18
    dih2dimb.p
    simprd
    #
    wph
    @16
    @20
    dih2dimb.q
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
    @18
    @20
    wa
    @14
    wb
    wph
    @9
    @25
    @17
    cK
    hllat
    syl
    wph
    @15
    @26
    @19
    cA
    @12
    cP
    cK
    @22
    dih2dimb.a
    atbase
    syl
    #
    wph
    @16
    @27
    @21
    cA
    @12
    cQ
    cK
    @22
    dih2dimb.a
    atbase
    syl
    #
    wph
    @10
    @28
    wph
    @9
    @10
    dih2dimb.k
    simprd
    @12
    cH
    cK
    cW
    @22
    dih2dimb.h
    lhpbase
    syl
    @12
    c.or
    cK
    c.le
    cP
    cQ
    cW
    @22
    dih2dimb.l
    dih2dimb.j
    latjle12
    syl13anc
    mpbi2and
    @12
    @1
    cH
    cI
    cK
    c.le
    chlt
    cW
    @0
    @22
    dih2dimb.l
    dih2dimb.h
    dih2dimb.i
    @8
    dihvalb
    syl12anc
    wph
    @6
    @3
    @7
    @4
    c.po
    wph
    @11
    @26
    @18
    @6
    @3
    wceq
    dih2dimb.k
    @29
    @23
    @12
    @1
    cH
    cI
    cK
    c.le
    chlt
    cW
    cP
    @22
    dih2dimb.l
    dih2dimb.h
    dih2dimb.i
    @8
    dihvalb
    syl12anc
    wph
    @11
    @27
    @20
    @7
    @4
    wceq
    dih2dimb.k
    @30
    @24
    @12
    @1
    cH
    cI
    cK
    c.le
    chlt
    cW
    cQ
    @22
    dih2dimb.l
    dih2dimb.h
    dih2dimb.i
    @8
    dihvalb
    syl12anc
    oveq12d
    3sstr4d
end
