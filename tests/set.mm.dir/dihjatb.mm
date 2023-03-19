include "co.mm"
include "cfv.mm"
include "dih2dimb.mm"
include "cbs.mm"
include "eqid.mm"
include "wcel.mm"
include "wbr.mm"
include "simpld.mm"
include "atbase.mm"
include "syl.mm"
include "dihsumssj.mm"
include "eqssd.mm"

theorem dihjatb
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
  assume dihjatb.l: |- .<_ = ( le ` K )
  assume dihjatb.h: |- H = ( LHyp ` K )
  assume dihjatb.j: |- .\/ = ( join ` K )
  assume dihjatb.a: |- A = ( Atoms ` K )
  assume dihjatb.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjatb.s: |- .(+) = ( LSSum ` U )
  assume dihjatb.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjatb.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjatb.p: |- ( ph -> ( P e. A /\ P .<_ W ) )
  assume dihjatb.q: |- ( ph -> ( Q e. A /\ Q .<_ W ) )


  assert |- ( ph -> ( I ` ( P .\/ Q ) ) = ( ( I ` P ) .(+) ( I ` Q ) ) )

  proof
    wph
    cP
    cQ
    c.or
    co
    cI
    cfv
    cP
    cI
    cfv
    cQ
    cI
    cfv
    c.po
    co
    wph
    cA
    cP
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    c.le
    cW
    dihjatb.l
    dihjatb.j
    dihjatb.a
    dihjatb.h
    dihjatb.u
    dihjatb.s
    dihjatb.i
    dihjatb.k
    dihjatb.p
    dihjatb.q
    dih2dimb
    wph
    cK
    cbs
    cfv
    #
    c.po
    cU
    cH
    cI
    c.or
    cK
    cW
    cP
    cQ
    @0
    eqid
    #
    dihjatb.h
    dihjatb.j
    dihjatb.u
    dihjatb.s
    dihjatb.i
    dihjatb.k
    wph
    cP
    cA
    wcel
    #
    cP
    @0
    wcel
    wph
    @2
    cP
    cW
    c.le
    wbr
    dihjatb.p
    simpld
    cA
    @0
    cP
    cK
    @1
    dihjatb.a
    atbase
    syl
    wph
    cQ
    cA
    wcel
    #
    cQ
    @0
    wcel
    wph
    @3
    cQ
    cW
    c.le
    wbr
    dihjatb.q
    simpld
    cA
    @0
    cQ
    cK
    @1
    dihjatb.a
    atbase
    syl
    dihsumssj
    eqssd
end
