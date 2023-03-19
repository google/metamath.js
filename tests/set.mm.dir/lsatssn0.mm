include "csn.mm"
include "wss.mm"
include "wne.mm"
include "wpss.mm"
include "clmod.mm"
include "wcel.mm"
include "clss.mm"
include "cfv.mm"
include "eqid.mm"
include "lsatlssel.mm"
include "lss0ss.mm"
include "syl2anc.mm"
include "lsatn0.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "psssstrd.mm"
include "pssned.mm"

theorem lsatssn0
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let cU: class U
  let cW: class W
  let c.0: class .0.
  assume lsatssn0.o: |- .0. = ( 0g ` W )
  assume lsatssn0.a: |- A = ( LSAtoms ` W )
  assume lsatssn0.w: |- ( ph -> W e. LMod )
  assume lsatssn0.q: |- ( ph -> Q e. A )
  assume lsatssn0.u: |- ( ph -> Q C_ U )


  assert |- ( ph -> U =/= { .0. } )

  proof
    wph
    c.0
    csn
    #
    cU
    wph
    @0
    cU
    wph
    @0
    cQ
    cU
    wph
    @0
    cQ
    wss
    #
    @0
    cQ
    wne
    @0
    cQ
    wpss
    wph
    cW
    clmod
    wcel
    cQ
    cW
    clss
    cfv
    #
    wcel
    @1
    lsatssn0.w
    wph
    cA
    @2
    cQ
    cW
    @2
    eqid
    #
    lsatssn0.a
    lsatssn0.w
    lsatssn0.q
    lsatlssel
    @2
    cW
    cQ
    c.0
    lsatssn0.o
    @3
    lss0ss
    syl2anc
    wph
    cQ
    @0
    wph
    cA
    cQ
    cW
    c.0
    lsatssn0.o
    lsatssn0.a
    lsatssn0.w
    lsatssn0.q
    lsatn0
    necomd
    @0
    cQ
    df-pss
    sylanbrc
    lsatssn0.u
    psssstrd
    pssned
    necomd
end
