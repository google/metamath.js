include "co.mm"
include "wceq.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "cif.mm"
include "eqid.mm"
include "pmat1ovd.mm"
include "crg.mm"
include "wcel.mm"
include "ply1scl1.mm"
include "syl.mm"
include "eqcomd.mm"
include "ply1scl0.mm"
include "ifeq12d.mm"
include "eqtrd.mm"

theorem pmat1ovscd
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cJ: class J
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  assume pmat0opsc.p: |- P = ( Poly1 ` R )
  assume pmat0opsc.c: |- C = ( N Mat P )
  assume pmat0opsc.a: |- A = ( algSc ` P )
  assume pmat0opsc.z: |- .0. = ( 0g ` R )
  assume pmat1opsc.o: |- .1. = ( 1r ` R )
  assume pmat1ovscd.n: |- ( ph -> N e. Fin )
  assume pmat1ovscd.r: |- ( ph -> R e. Ring )
  assume pmat1ovscd.i: |- ( ph -> I e. N )
  assume pmat1ovscd.j: |- ( ph -> J e. N )
  assume pmat1ovscd.u: |- U = ( 1r ` C )


  assert |- ( ph -> ( I U J ) = if ( I = J , ( A ` .1. ) , ( A ` .0. ) ) )

  proof
    wph
    cI
    cJ
    cU
    co
    cI
    cJ
    wceq
    #
    cP
    cur
    cfv
    #
    cP
    c0g
    cfv
    #
    cif
    @0
    c.1
    cA
    cfv
    #
    c.0
    cA
    cfv
    #
    cif
    wph
    cC
    cP
    cR
    cU
    @1
    cI
    cJ
    cN
    @2
    pmat0opsc.p
    pmat0opsc.c
    @2
    eqid
    #
    @1
    eqid
    #
    pmat1ovscd.n
    pmat1ovscd.r
    pmat1ovscd.i
    pmat1ovscd.j
    pmat1ovscd.u
    pmat1ovd
    wph
    @0
    @1
    @3
    @2
    @4
    wph
    @3
    @1
    wph
    cR
    crg
    wcel
    #
    @3
    @1
    wceq
    pmat1ovscd.r
    cA
    cP
    cR
    c.1
    @1
    pmat0opsc.p
    pmat0opsc.a
    pmat1opsc.o
    @6
    ply1scl1
    syl
    eqcomd
    wph
    @4
    @2
    wph
    @7
    @4
    @2
    wceq
    pmat1ovscd.r
    cA
    cP
    cR
    @2
    c.0
    pmat0opsc.p
    pmat0opsc.a
    pmat0opsc.z
    @5
    ply1scl0
    syl
    eqcomd
    ifeq12d
    eqtrd
end
