include "cbs.mm"
include "cfv.mm"
include "cmee.mm"
include "co.mm"
include "eqid.mm"
include "coc.mm"
include "cv.mm"
include "wceq.mm"
include "cltrn.mm"
include "crio.mm"
include "ctrl.mm"
include "ctendo.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "ccnv.mm"
include "cid.mm"
include "cres.mm"
include "dihjatcclem4.mm"
include "dihjatcclem2.mm"

theorem dihjatcc
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
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  assume dihjatcc.l: |- .<_ = ( le ` K )
  assume dihjatcc.h: |- H = ( LHyp ` K )
  assume dihjatcc.j: |- .\/ = ( join ` K )
  assume dihjatcc.a: |- A = ( Atoms ` K )
  assume dihjatcc.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjatcc.s: |- .(+) = ( LSSum ` U )
  assume dihjatcc.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjatcc.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjatcc.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )
  assume dihjatcc.q: |- ( ph -> ( Q e. A /\ -. Q .<_ W ) )


  assert |- ( ph -> ( I ` ( P .\/ Q ) ) = ( ( I ` P ) .(+) ( I ` Q ) ) )

  proof
    wph
    cA
    cK
    cbs
    cfv
    #
    cP
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    c.le
    cK
    cmee
    cfv
    #
    cP
    cQ
    c.or
    co
    cW
    @1
    co
    #
    cW
    @0
    eqid
    #
    dihjatcc.l
    dihjatcc.h
    dihjatcc.j
    @1
    eqid
    #
    dihjatcc.a
    dihjatcc.u
    dihjatcc.s
    dihjatcc.i
    @2
    eqid
    #
    dihjatcc.k
    dihjatcc.p
    dihjatcc.q
    wph
    cA
    @0
    cW
    cK
    coc
    cfv
    cfv
    #
    @6
    vd
    cv
    #
    cfv
    #
    cQ
    wceq
    vd
    cW
    cK
    cltrn
    cfv
    cfv
    #
    crio
    #
    cP
    c.po
    cQ
    cW
    cK
    ctrl
    cfv
    cfv
    #
    @9
    cU
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @8
    cP
    wceq
    vd
    @9
    crio
    #
    cH
    cI
    va
    vb
    @12
    @12
    vd
    @9
    @7
    va
    cv
    cfv
    #
    @7
    vb
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    c.or
    cK
    c.le
    @1
    va
    @12
    vd
    @9
    @14
    ccnv
    cmpt
    cmpt
    #
    @2
    cW
    vd
    @9
    cid
    @0
    cres
    cmpt
    #
    va
    vb
    vd
    @3
    dihjatcc.l
    dihjatcc.h
    dihjatcc.j
    @4
    dihjatcc.a
    dihjatcc.u
    dihjatcc.s
    dihjatcc.i
    @5
    dihjatcc.k
    dihjatcc.p
    dihjatcc.q
    @6
    eqid
    @9
    eqid
    @11
    eqid
    @12
    eqid
    @13
    eqid
    @10
    eqid
    @16
    eqid
    @17
    eqid
    @15
    eqid
    dihjatcclem4
    dihjatcclem2
end
