include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "ctp.mm"
include "cop.mm"
include "wf.mm"
include "3pm3.2i.mm"
include "ftpg.mm"
include "mp3an.mm"

theorem ftp
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ftp.a: |- A e. _V
  assume ftp.b: |- B e. _V
  assume ftp.c: |- C e. _V
  assume ftp.d: |- X e. _V
  assume ftp.e: |- Y e. _V
  assume ftp.f: |- Z e. _V
  assume ftp.g: |- A =/= B
  assume ftp.h: |- A =/= C
  assume ftp.i: |- B =/= C


  assert |- { <. A , X >. , <. B , Y >. , <. C , Z >. } : { A , B , C } --> { X , Y , Z }

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    w3a
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    w3a
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    cA
    cB
    cC
    ctp
    cX
    cY
    cZ
    ctp
    cA
    cX
    cop
    cB
    cY
    cop
    cC
    cZ
    cop
    ctp
    wf
    @0
    @1
    @2
    ftp.a
    ftp.b
    ftp.c
    3pm3.2i
    @3
    @4
    @5
    ftp.d
    ftp.e
    ftp.f
    3pm3.2i
    @6
    @7
    @8
    ftp.g
    ftp.h
    ftp.i
    3pm3.2i
    cX
    cY
    cZ
    cvv
    cvv
    cvv
    cvv
    cvv
    cvv
    cA
    cB
    cC
    ftpg
    mp3an
end
