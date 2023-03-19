include "c0.mm"
include "csupp.mm"
include "co.mm"
include "cep.mm"
include "wwe.mm"
include "cdm.mm"
include "com.mm"
include "wcel.mm"
include "con0.mm"
include "wss.mm"
include "suppssdm.mm"
include "wf.mm"
include "wceq.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "onss.mm"
include "sstrd.mm"
include "epweon.mm"
include "wess.mm"
include "mpisyl.mm"
include "cfn.mm"
include "cin.mm"
include "cvv.mm"
include "ovexd.mm"
include "oion.mm"
include "cen.mm"
include "simprd.mm"
include "fsuppimpd.mm"
include "oien.mm"
include "syl2anc.mm"
include "enfii.mm"
include "elind.mm"
include "onfin2.mm"
include "syl6eleqr.mm"
include "jca.mm"

theorem cantnfcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cT: class T
  let cZ: class Z
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnfcl.g: |- G = OrdIso ( _E , ( F supp (/) ) )
  assume cantnfcl.f: |- ( ph -> F e. S )


  assert |- ( ph -> ( _E We ( F supp (/) ) /\ dom G e. _om ) )

  proof
    wph
    cF
    c0
    csupp
    co
    #
    cep
    wwe
    #
    cG
    cdm
    #
    com
    wcel
    wph
    @0
    con0
    wss
    con0
    cep
    wwe
    @1
    wph
    @0
    cB
    con0
    wph
    cF
    cdm
    #
    @0
    cB
    cF
    c0
    suppssdm
    wph
    cB
    cA
    cF
    wf
    #
    @3
    cB
    wceq
    wph
    @4
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    @4
    @5
    wa
    cantnfcl.f
    wph
    cA
    cB
    cS
    cF
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    mpbid
    #
    simpld
    cB
    cA
    cF
    fdm
    syl
    syl5sseq
    wph
    cB
    con0
    wcel
    cB
    con0
    wss
    cantnfs.b
    cB
    onss
    syl
    sstrd
    epweon
    @0
    con0
    cep
    wess
    mpisyl
    #
    wph
    @2
    con0
    cfn
    cin
    com
    wph
    con0
    cfn
    @2
    wph
    @0
    cvv
    wcel
    #
    @2
    con0
    wcel
    wph
    cF
    c0
    csupp
    ovexd
    #
    @0
    cep
    cG
    cvv
    cantnfcl.g
    oion
    syl
    wph
    @0
    cfn
    wcel
    @2
    @0
    cen
    wbr
    #
    @2
    cfn
    wcel
    wph
    cF
    c0
    wph
    @4
    @5
    @6
    simprd
    fsuppimpd
    wph
    @8
    @1
    @10
    @9
    @7
    @0
    cep
    cG
    cvv
    cantnfcl.g
    oien
    syl2anc
    @2
    @0
    enfii
    syl2anc
    elind
    onfin2
    syl6eleqr
    jca
end
