include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "clvec.mm"
include "adantr.mm"
include "simpr.mm"
include "wne.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simprd.mm"
include "lsatel.mm"
include "wss.mm"
include "eqimss2.mm"
include "adantl.mm"
include "wb.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "eldifad.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "impbida.mm"

theorem lsatelbN
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lsatelb.v: |- V = ( Base ` W )
  assume lsatelb.o: |- .0. = ( 0g ` W )
  assume lsatelb.n: |- N = ( LSpan ` W )
  assume lsatelb.a: |- A = ( LSAtoms ` W )
  assume lsatelb.w: |- ( ph -> W e. LVec )
  assume lsatelb.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lsatelb.u: |- ( ph -> U e. A )


  assert |- ( ph -> ( X e. U <-> U = ( N ` { X } ) ) )

  proof
    wph
    cX
    cU
    wcel
    #
    cU
    cX
    csn
    cN
    cfv
    #
    wceq
    #
    wph
    @0
    wa
    cA
    cU
    cN
    cW
    cX
    c.0
    lsatelb.o
    lsatelb.n
    lsatelb.a
    wph
    cW
    clvec
    wcel
    #
    @0
    lsatelb.w
    adantr
    wph
    cU
    cA
    wcel
    @0
    lsatelb.u
    adantr
    wph
    @0
    simpr
    wph
    cX
    c.0
    wne
    #
    @0
    wph
    cX
    cV
    wcel
    #
    @4
    wph
    cX
    cV
    c.0
    csn
    #
    cdif
    wcel
    @5
    @4
    wa
    lsatelb.x
    cX
    cV
    c.0
    eldifsn
    sylib
    simprd
    adantr
    lsatel
    wph
    @2
    wa
    @0
    @1
    cU
    wss
    #
    @2
    @7
    wph
    @1
    cU
    eqimss2
    adantl
    wph
    @0
    @7
    wb
    @2
    wph
    cW
    clss
    cfv
    #
    cU
    cN
    cV
    cW
    cX
    lsatelb.v
    @8
    eqid
    #
    lsatelb.n
    wph
    @3
    cW
    clmod
    wcel
    lsatelb.w
    cW
    lveclmod
    syl
    #
    wph
    cA
    @8
    cU
    cW
    @9
    lsatelb.a
    @10
    lsatelb.u
    lsatlssel
    wph
    cX
    cV
    @6
    lsatelb.x
    eldifad
    lspsnel5
    adantr
    mpbird
    impbida
end
