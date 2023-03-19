include "ccnf.mm"
include "co.mm"
include "cfv.mm"
include "c0.mm"
include "csupp.mm"
include "cep.mm"
include "coi.mm"
include "cdm.mm"
include "cvv.mm"
include "cv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "eqid.mm"
include "cantnfval.mm"
include "wcel.mm"
include "con0.mm"
include "csuc.mm"
include "ssexd.mm"
include "oion.mm"
include "sucidg.mm"
include "3syl.mm"
include "cima.mm"
include "wiso.mm"
include "wf1o.mm"
include "wfo.mm"
include "wceq.mm"
include "wwe.mm"
include "com.mm"
include "cantnfcl.mm"
include "simpld.mm"
include "oiiso.mm"
include "syl2anc.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "foima.mm"
include "4syl.mm"
include "eqsstrd.mm"
include "cantnflt.mm"
include "eqeltrd.mm"

theorem cantnflt2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
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
  let cD: class D
  let cM: class M
  let cT: class T
  let cZ: class Z
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnflt2.f: |- ( ph -> F e. S )
  assume cantnflt2.a: |- ( ph -> (/) e. A )
  assume cantnflt2.c: |- ( ph -> C e. On )
  assume cantnflt2.s: |- ( ph -> ( F supp (/) ) C_ C )


  assert |- ( ph -> ( ( A CNF B ) ` F ) e. ( A ^o C ) )

  proof
    wph
    cF
    cA
    cB
    ccnf
    co
    cfv
    cF
    c0
    csupp
    co
    #
    cep
    coi
    #
    cdm
    #
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    @1
    cfv
    #
    coe
    co
    @3
    cF
    cfv
    comu
    co
    vz
    cv
    coa
    co
    cmpt2
    c0
    cseqom
    #
    cfv
    cA
    cC
    coe
    co
    wph
    vz
    cA
    cB
    cS
    vk
    cF
    @1
    @4
    cantnfs.s
    cantnfs.a
    cantnfs.b
    @1
    eqid
    #
    cantnflt2.f
    @4
    eqid
    #
    cantnfval
    wph
    vz
    cA
    cB
    cC
    cS
    vk
    cF
    @1
    @4
    @2
    cantnfs.s
    cantnfs.a
    cantnfs.b
    @5
    cantnflt2.f
    @6
    cantnflt2.a
    wph
    @0
    cvv
    wcel
    #
    @2
    con0
    wcel
    @2
    @2
    csuc
    wcel
    wph
    @0
    cC
    con0
    cantnflt2.c
    cantnflt2.s
    ssexd
    #
    @0
    cep
    @1
    cvv
    @5
    oion
    @2
    con0
    sucidg
    3syl
    cantnflt2.c
    wph
    @1
    @2
    cima
    #
    @0
    cC
    wph
    @2
    @0
    cep
    cep
    @1
    wiso
    #
    @2
    @0
    @1
    wf1o
    @2
    @0
    @1
    wfo
    @9
    @0
    wceq
    wph
    @7
    @0
    cep
    wwe
    #
    @10
    @8
    wph
    @11
    @2
    com
    wcel
    wph
    cA
    cB
    cS
    cF
    @1
    cantnfs.s
    cantnfs.a
    cantnfs.b
    @5
    cantnflt2.f
    cantnfcl
    simpld
    @0
    cep
    @1
    cvv
    @5
    oiiso
    syl2anc
    @2
    @0
    cep
    cep
    @1
    isof1o
    @2
    @0
    @1
    f1ofo
    @2
    @0
    @1
    foima
    4syl
    cantnflt2.s
    eqsstrd
    cantnflt
    eqeltrd
end
