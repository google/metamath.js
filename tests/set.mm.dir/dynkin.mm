include "cv.mm"
include "wss.mm"
include "csiga.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "wcel.mm"
include "cin.mm"
include "sseq2.mm"
include "cbvrabv.mm"
include "inteqi.mm"
include "ldgenpisys.mm"
include "cpw.mm"
include "cfn.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "ispisys2.mm"
include "simplbi.mm"
include "syl.mm"
include "elpwid.mm"
include "ldsysgenld.mm"
include "elind.mm"
include "sigapildsys.mm"
include "syl6eleqr.mm"
include "ssintub.mm"
include "a1i.mm"
include "intminss.mm"
include "syl2anc.mm"
include "sstrd.mm"

theorem dynkin
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cP: class P
  let cS: class S
  let cT: class T
  let cL: class L
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vt: setvar t
  let vz: setvar z
  let vv: setvar v
  assume dynkin.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }
  assume dynkin.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }
  assume dynkin.o: |- ( ph -> O e. V )
  assume dynkin.1: |- ( ph -> S e. L )
  assume dynkin.2: |- ( ph -> T e. P )
  assume dynkin.3: |- ( ph -> T C_ S )

  disjoint s x
  disjoint s y
  disjoint x y
  disjoint L x
  disjoint L y
  disjoint O s
  disjoint O x
  disjoint P x
  disjoint P y
  disjoint L s
  disjoint L u
  disjoint s u
  disjoint u x
  disjoint O u
  disjoint T s
  disjoint T u
  disjoint T x
  disjoint ph x
  disjoint O y
  disjoint T y
  disjoint V x
  disjoint ph y
  disjoint f i
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i n
  disjoint i s
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint s t
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x z
  disjoint y z
  disjoint L f
  disjoint L i
  disjoint L n
  disjoint L t
  disjoint O t
  disjoint P f
  disjoint P i
  disjoint P n
  disjoint P t
  disjoint t u
  disjoint S t
  disjoint T t
  disjoint ph t
  disjoint L v
  disjoint s v
  disjoint u v
  disjoint O v
  disjoint v y
  disjoint S v
  disjoint T v
  disjoint ph v
  disjoint t v
  disjoint v x
  assert |- ( ph -> |^| { u e. ( sigAlgebra ` O ) | T C_ u } C_ S )

  proof
    wph
    cT
    vu
    cv
    #
    wss
    #
    vu
    cO
    csiga
    cfv
    #
    crab
    cint
    #
    cT
    vv
    cv
    #
    wss
    #
    vv
    cL
    crab
    #
    cint
    #
    cS
    wph
    @7
    @2
    wcel
    cT
    @7
    wss
    #
    @3
    @7
    wss
    wph
    @7
    cP
    cL
    cin
    @2
    wph
    cP
    cL
    @7
    wph
    vx
    vy
    vt
    cP
    cT
    @7
    cL
    cO
    cV
    vs
    dynkin.p
    dynkin.l
    dynkin.o
    @6
    cT
    vt
    cv
    #
    wss
    #
    vt
    cL
    crab
    @5
    @10
    vv
    vt
    cL
    @4
    @9
    cT
    sseq2
    cbvrabv
    inteqi
    dynkin.2
    ldgenpisys
    wph
    vx
    vy
    vv
    cT
    cL
    cO
    cV
    vs
    dynkin.l
    dynkin.o
    wph
    cT
    cO
    cpw
    #
    wph
    cT
    cP
    wcel
    #
    cT
    @11
    cpw
    wcel
    #
    dynkin.2
    @12
    @13
    vx
    cv
    cint
    cT
    wcel
    vx
    cT
    cpw
    cfn
    cin
    c0
    csn
    cdif
    wral
    vx
    cP
    cT
    cO
    vs
    dynkin.p
    ispisys2
    simplbi
    syl
    elpwid
    ldsysgenld
    elind
    vx
    vy
    cP
    cL
    cO
    vs
    dynkin.p
    dynkin.l
    sigapildsys
    syl6eleqr
    @8
    wph
    vv
    cT
    cL
    ssintub
    a1i
    @1
    @8
    vu
    @7
    @2
    @0
    @7
    cT
    sseq2
    intminss
    syl2anc
    wph
    cS
    cL
    wcel
    cT
    cS
    wss
    #
    @7
    cS
    wss
    dynkin.1
    dynkin.3
    @5
    @14
    vv
    cS
    cL
    @4
    cS
    cT
    sseq2
    intminss
    syl2anc
    sstrd
end
