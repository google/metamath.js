include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "crab.mm"
include "ccnf.mm"
include "cdm.mm"
include "eqid.mm"
include "cantnfdm.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "syl6bb.mm"
include "con0.mm"
include "elmapd.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem cantnfs
  let wph: wff ph
  let cA: class A
  let cB: class B
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
  let cC: class C
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


  assert |- ( ph -> ( F e. S <-> ( F : B --> A /\ F finSupp (/) ) ) )

  proof
    wph
    cF
    cS
    wcel
    #
    cF
    cA
    cB
    cmap
    co
    #
    wcel
    #
    cF
    c0
    cfsupp
    wbr
    #
    wa
    #
    cB
    cA
    cF
    wf
    #
    @3
    wa
    wph
    @0
    cF
    vg
    cv
    #
    c0
    cfsupp
    wbr
    #
    vg
    @1
    crab
    #
    wcel
    @4
    wph
    cS
    @8
    cF
    wph
    cS
    cA
    cB
    ccnf
    co
    cdm
    @8
    cantnfs.s
    wph
    cA
    cB
    @8
    vg
    @8
    eqid
    cantnfs.a
    cantnfs.b
    cantnfdm
    syl5eq
    eleq2d
    @7
    @3
    vg
    cF
    @1
    @6
    cF
    c0
    cfsupp
    breq1
    elrab
    syl6bb
    wph
    @2
    @5
    @3
    wph
    cA
    cB
    cF
    con0
    con0
    cantnfs.a
    cantnfs.b
    elmapd
    anbi1d
    bitrd
end
