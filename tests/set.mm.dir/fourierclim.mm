include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cc0.mm"
include "cfv.mm"
include "cmin.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cr.mm"
include "wf.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "adantl.mm"
include "cpi.mm"
include "cneg.mm"
include "cioo.mm"
include "cdm.mm"
include "cdif.mm"
include "cfn.mm"
include "cc.mm"
include "ccncf.mm"
include "cico.mm"
include "cpnf.mm"
include "cres.mm"
include "climc.mm"
include "c0.mm"
include "wne.mm"
include "cioc.mm"
include "cmnf.mm"
include "fourierclimd.mm"
include "trud.mm"

theorem fourierclim
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cL: class L
  let cX: class X
  let vk: setvar k
  assume fourierclim.f: |- F : RR --> RR
  assume fourierclim.t: |- T = ( 2 x. _pi )
  assume fourierclim.per: |- ( x e. RR -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierclim.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fourierclim.dmdv: |- ( ( -u _pi (,) _pi ) \ dom G ) e. Fin
  assume fourierclim.dvcn: |- G e. ( dom G -cn-> CC )
  assume fourierclim.rlim: |- ( x e. ( ( -u _pi [,) _pi ) \ dom G ) -> ( ( G |` ( x (,) +oo ) ) limCC x ) =/= (/) )
  assume fourierclim.llim: |- ( x e. ( ( -u _pi (,] _pi ) \ dom G ) -> ( ( G |` ( -oo (,) x ) ) limCC x ) =/= (/) )
  assume fourierclim.x: |- X e. RR
  assume fourierclim.l: |- L e. ( ( F |` ( -oo (,) X ) ) limCC X )
  assume fourierclim.r: |- R e. ( ( F |` ( X (,) +oo ) ) limCC X )
  assume fourierclim.a: |- A = ( n e. NN0 |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierclim.b: |- B = ( n e. NN |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierclim.s: |- S = ( n e. NN |-> ( ( ( A ` n ) x. ( cos ` ( n x. X ) ) ) + ( ( B ` n ) x. ( sin ` ( n x. X ) ) ) ) )

  disjoint F n
  disjoint F x
  disjoint n x
  disjoint G x
  disjoint T x
  disjoint X n
  disjoint X x
  disjoint k x
  assert |- seq 1 ( + , S ) ~~> ( ( ( L + R ) / 2 ) - ( ( A ` 0 ) / 2 ) )

  proof
    caddc
    cS
    c1
    cseq
    cL
    cR
    caddc
    co
    c2
    cdiv
    co
    cc0
    cA
    cfv
    c2
    cdiv
    co
    cmin
    co
    cli
    wbr
    wtru
    vx
    cA
    cB
    cR
    cS
    cT
    vn
    cF
    cG
    cL
    cX
    cr
    cr
    cF
    wf
    wtru
    fourierclim.f
    a1i
    fourierclim.t
    vx
    cv
    #
    cr
    wcel
    @0
    cT
    caddc
    co
    cF
    cfv
    @0
    cF
    cfv
    wceq
    wtru
    fourierclim.per
    adantl
    fourierclim.g
    cpi
    cneg
    #
    cpi
    cioo
    co
    cG
    cdm
    #
    cdif
    cfn
    wcel
    wtru
    fourierclim.dmdv
    a1i
    cG
    @2
    cc
    ccncf
    co
    wcel
    wtru
    fourierclim.dvcn
    a1i
    @0
    @1
    cpi
    cico
    co
    @2
    cdif
    wcel
    cG
    @0
    cpnf
    cioo
    co
    cres
    @0
    climc
    co
    c0
    wne
    wtru
    fourierclim.rlim
    adantl
    @0
    @1
    cpi
    cioc
    co
    @2
    cdif
    wcel
    cG
    cmnf
    @0
    cioo
    co
    cres
    @0
    climc
    co
    c0
    wne
    wtru
    fourierclim.llim
    adantl
    cX
    cr
    wcel
    wtru
    fourierclim.x
    a1i
    cL
    cF
    cmnf
    cX
    cioo
    co
    cres
    cX
    climc
    co
    wcel
    wtru
    fourierclim.l
    a1i
    cR
    cF
    cX
    cpnf
    cioo
    co
    cres
    cX
    climc
    co
    wcel
    wtru
    fourierclim.r
    a1i
    fourierclim.a
    fourierclim.b
    fourierclim.s
    fourierclimd
    trud
end
